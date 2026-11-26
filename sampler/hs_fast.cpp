// hs_fast.cpp: the Gibbs kernel of hs_fast() (see hsfast.R), compiled with Rcpp / RcppArmadillo when hsfast.R is source()d.
// This code implements the Gibbs sampler of the R package 'horseshoe' (van der Pas, Scott, Chakraborty and Bhattacharya),
// version 0.2.0, with structured linear algebra for the draw of theta. It is distributed under GPL-3 (see sampler/LICENSE).
//
// How it relates to the package's sampler (same random draws, in the same order):
//   (1) the theta / lambda / tau / s2 updates of the sweep are written as the functions draw_theta, update_lambda,
//       update_tau, update_s2, so that a Geweke test can run the same code block by block;
//   (2) argument clamp, a bit mask that switches the package's numerical floors on:
//         bit 1 = the package's lambda floor  Fub  >= 1e-4  (horseshoe.R:187-188)
//         bit 2 = the package's tau floor     Fubt >= 1e-8  (horseshoe.R:200-201)
//         bit 4 = the package's sigma^2 floors E1, E2 >= 1e-8  (horseshoe.R:231-232)
//       clamp = 7 is the package's arithmetic; clamp = 0 is the exact (floorless) posterior everywhere, written with
//       expm1 / log1p and the log-scale gamma CDF / quantile. Same RNG draws, same order.
//   (3) exported names carry the hsfast_ prefix (hsfast_kernel, hsfast_fixed_draws, hsfast_dense_factor).
//   (4) Jeffreys RSS = ||y - X theta||^2 from the residual, as the package (the Gram expansion
//       y'y - 2 theta'X'y + theta'G theta cancels catastrophically); the exact tau slice clamps only a
//       finite round-off overshoot (relative 1e-12) and uses the zero-rate limit; every update validates its output and stops on an
//       invalid state; factorisations stop when G + diag(w) is not numerically positive definite.
//   (5) one sweep = one_sweep(), shared by the sampler and a Geweke-test driver.
//   (6) accuracy check ("guard") of the dense theta draw (exact mode only, argument guard = 1 of hsfast_kernel):
//       every sweep, with G and D = diag(w) applied SEPARATELY (never through the formed sum G + D, whose rounding can drop D),
//         e      = (G theta + D theta) - L (L^T theta)                   backward error of the computed factor on the drawn vector
//         r      = ||e|| / ||G theta + D theta||                         (2-norm; recorded)
//         r_w    = ||L^{-1} e|| / ||L^T theta||                          (the same error in the factor's own metric; GUARDED)
//         r_mean = ||G mu + D mu - X'y|| / ||X'y||                       (mean-solve residual; GUARDED)
//       stop if r_w > 1e-8 or r_mean > 1e-8. r_w is guarded instead of r because r is dominated by the well-determined directions:
//       on a test design with x = (100000002, 100000003), G + D rounds to G and r is only 1e-9..1.5e-8 per draw, while r_w is 3e-3..0.4.
//       The guard reads theta, mu, L, G and w and writes only its own statistics: no RNG draw, no change to theta (bit-identical draws).
//   (7) lambda_mean: the running sum of lambda over the SAVED sweeps (the sweeps whose theta is
//       written to draws), divided by nsave; returned as list element lambda_mean (hs_fast's LambdaHat). It reads lambda only: no RNG
//       draw, no change to the chain (draws, tau, s2 and the RNG stream are the same as without it).
//
// RNG order and formulas per sweep = the package's (algo 2, p <= n):
//   theta : z = rnorm(p) (R::norm_rand x p);  theta = mu + sigma L^{-T} z,  A = G + diag(1/(tau lambda)^2) = L L^T,
//           mu = L^{-T} L^{-1} X'y.  (package: U = chol(A/s2), Beta = solve(U, solve(t(U), X'y/s2)) + solve(U, z); same map)
//   lambda: upsi = runif(p, 0, 1/(1+eta)) [vector 1]; Fub = max(1-exp(-tempps ub), 1e-4); up = runif(p, 0, Fub) [vector 2];
//           eta = -log(1-up)/tempps
//   tau   : (halfCauchy) utau = runif(0, 1/(1+et)); Fubt = max(pgamma(ubt, (p+1)/2, scale = 1/tempt), 1e-8);
//           ut = runif(0, Fubt); et = qgamma(ut, ...)
//   s2    : (Jeffreys) s2 = 1/rgamma((n+p)/2, scale = 2/(E1+E2)); E1 = max(RSS, 1e-8), RSS = ||y - X theta||^2;
//           E2 = max(sum theta^2/(tau lambda)^2, 1e-8)   (floors: clamp bit 4 only)
// Exact forms (clamp bit off), with V the same uniform the package would scale (R::runif(0, F) = F * unif_rand()):
//   lambda: x = tempps ub; Fub = -expm1(-x); eta = -log1p(-Fub V)/tempps;  x < 1e-300: eta = ub V (the t -> 0 limit; exact at t = 0)
//   tau   : log Fubt = pgamma(ubt, ..., log.p = TRUE); et = qgamma(log Fubt + log V, ..., log.p = TRUE); a finite overshoot
//           et in (ubt, ubt (1 + 1e-12)] is round-off and set to ubt, anything else invalid stops; tempt ubt < 1e-300: et = ubt V^(1/shape)
//           (the zero-rate limit of the truncated gamma)
//   s2    : E1 = RSS, E2 = sum theta^2/(tau lambda)^2 with no floor; E1 + E2 must be positive and finite, else stop
// Structured factorisations of A (gram$type):
//   0 dense  : LAPACK Cholesky
//   1 diag   : L = sqrt(d + w)
//   2 band   : banded Cholesky, lower band (bw+1) x p, Gb(k, j) = G(j+k, j)
//   3 semisep: G = diag(d) + U U^T (U p x r). L = chol(D + U U^T), D = diag(d + w), obtained by r classical positive
//              rank-one Cholesky updates of D^{1/2}. The factor stays "diagonal + semiseparable":
//              L = diag(ell) + tril_strict(U B^T), B p x r, so factor and solves cost O(p r^2) and O(p r).
// [[Rcpp::depends(RcppArmadillo)]]
#include <RcppArmadillo.h>
#include <cmath>
#include <chrono>
using namespace Rcpp;

struct Gram {
  int type; arma::mat G; arma::vec d; arma::mat U; arma::mat Gb; int bw;
  arma::vec mul(const arma::vec& v) const {
    if (type == 0) return G * v;
    if (type == 1) return d % v;
    if (type == 3) { arma::vec out = d % v; if (U.n_cols) out += U * (U.t() * v); return out; }
    int p = v.n_elem; arma::vec out(p, arma::fill::zeros);
    for (int j = 0; j < p; ++j) { out[j] += Gb(0, j) * v[j];
      for (int k = 1; k <= bw && j + k < p; ++k) { double g = Gb(k, j); out[j + k] += g * v[j]; out[j] += g * v[j + k]; } }
    return out;
  }
};
static Gram read_gram(List gram) {
  Gram g; g.type = as<int>(gram["type"]); g.bw = 0;
  if (g.type == 0) g.G = as<arma::mat>(gram["G"]);
  if (g.type == 1) g.d = as<arma::vec>(gram["d"]);
  if (g.type == 2) { g.Gb = as<arma::mat>(gram["Gb"]); g.bw = as<int>(gram["bw"]); }
  if (g.type == 3) { g.d = as<arma::vec>(gram["d"]); g.U = as<arma::mat>(gram["U"]); }
  return g;
}

// ---- band routines: in-place banded Cholesky factor and the two triangular solves, lower band storage B(k, j) = L(j+k, j)
static void band_chol(arma::mat& B, int bw) {
  int p = B.n_cols;
  for (int j = 0; j < p; ++j) {
    double s = B(0, j);
    for (int k = 1; k <= bw && j - k >= 0; ++k) s -= B(k, j - k) * B(k, j - k);
    if (!(s > 0)) Rcpp::stop("band_chol: matrix not positive definite");
    double ljj = std::sqrt(s); B(0, j) = ljj;
    for (int i = j + 1; i <= j + bw && i < p; ++i) {
      double t = B(i - j, j);
      for (int k = 1; k <= bw && j - k >= 0 && i - (j - k) <= bw; ++k) t -= B(i - (j - k), j - k) * B(k, j - k);
      B(i - j, j) = t / ljj;
    }
  }
}
static arma::vec band_fwd(const arma::mat& L, int bw, arma::vec b) {
  int p = b.n_elem;
  for (int i = 0; i < p; ++i) { double s = b[i];
    for (int k = 1; k <= bw && i - k >= 0; ++k) s -= L(k, i - k) * b[i - k];
    b[i] = s / L(0, i); }
  return b;
}
static arma::vec band_bwd(const arma::mat& L, int bw, arma::vec b) {
  int p = b.n_elem;
  for (int i = p - 1; i >= 0; --i) { double s = b[i];
    for (int k = 1; k <= bw && i + k < p; ++k) s -= L(k, i) * b[i + k];
    b[i] = s / L(0, i); }
  return b;
}

// ---- factor of A = G + diag(w)
struct Chol {
  int type; arma::mat L; arma::vec ell; arma::mat B; arma::mat Lb; const arma::mat* U; int bw;
};
static Chol factor(const Gram& g, const arma::vec& w) {
  Chol c; c.type = g.type; c.U = &g.U; c.bw = g.bw;
  int p = w.n_elem;
  if (!w.is_finite() || arma::any(w <= 0)) Rcpp::stop("hs_fast: invalid prior precision 1/(tau lambda)^2 (non-finite or not positive)");
  if (g.type == 0) { arma::mat A = g.G; A.diag() += w;
    if (!arma::chol(c.L, A, "lower")) Rcpp::stop("hs_fast: G + diag(1/(tau lambda)^2) is not numerically positive definite "
                                                 "(rank-deficient or badly scaled design with a weak prior); rescale X or use a stronger prior"); }
  else if (g.type == 1) { c.ell = arma::sqrt(g.d + w); }
  else if (g.type == 2) { c.Lb = g.Gb; c.Lb.row(0) += w.t(); band_chol(c.Lb, g.bw); }
  else {
    int r = g.U.n_cols; c.ell = arma::sqrt(g.d + w); c.B.zeros(p, r);
    std::vector<double> gam(r);
    for (int t = 0; t < r; ++t) {                       // rank-one update with column t of U
      std::fill(gam.begin(), gam.end(), 0.0); gam[t] = 1.0;
      for (int k = 0; k < p; ++k) {
        double vk = 0; for (int m = 0; m <= t; ++m) vk += g.U(k, m) * gam[m];
        if (vk == 0) continue;                           // c = 1, s = 0: nothing changes
        double lk = c.ell[k], rr = std::hypot(lk, vk), cc = rr / lk, ss = vk / lk;
        c.ell[k] = rr;
        for (int m = 0; m <= t; ++m) { double bnew = (c.B(k, m) + ss * gam[m]) / cc; c.B(k, m) = bnew; gam[m] = cc * gam[m] - ss * bnew; }
      }
    }
  }
  if ((g.type == 1 || g.type == 3) && (!c.ell.is_finite() || arma::any(c.ell <= 0)))
    Rcpp::stop("hs_fast: structured factor invalid (d + 1/(tau lambda)^2 must be positive and finite)");
  return c;
}
static arma::vec fwd(const Chol& c, const arma::vec& b) {      // solve L x = b
  if (c.type == 0) return arma::solve(arma::trimatl(c.L), b);
  if (c.type == 1) return b / c.ell;
  if (c.type == 2) return band_fwd(c.Lb, c.bw, b);
  int p = b.n_elem, r = c.B.n_cols; arma::vec x(p); std::vector<double> h(r, 0.0); const arma::mat& U = *c.U;
  for (int i = 0; i < p; ++i) { double s = b[i]; for (int m = 0; m < r; ++m) s -= U(i, m) * h[m];
    x[i] = s / c.ell[i]; for (int m = 0; m < r; ++m) h[m] += c.B(i, m) * x[i]; }
  return x;
}
static arma::vec bwd(const Chol& c, const arma::vec& b) {      // solve L^T x = b
  if (c.type == 0) return arma::solve(arma::trimatu(c.L.t()), b);
  if (c.type == 1) return b / c.ell;
  if (c.type == 2) return band_bwd(c.Lb, c.bw, b);
  int p = b.n_elem, r = c.B.n_cols; arma::vec x(p); std::vector<double> gq(r, 0.0); const arma::mat& U = *c.U;
  for (int i = p - 1; i >= 0; --i) { double s = b[i]; for (int m = 0; m < r; ++m) s -= c.B(i, m) * gq[m];
    x[i] = s / c.ell[i]; for (int m = 0; m < r; ++m) gq[m] += U(i, m) * x[i]; }
  return x;
}

// ---------------------------------------------------------------- accuracy guard (change (6)); off unless hsfast_kernel(guard = 1)
struct GuardState { bool on = false; long sweep = 0; std::vector<double> r, rw, rmean; };
static GuardState g_guard;
struct GuardScope {                       // resets the guard on every exit from hsfast_kernel, including Rcpp::stop
  GuardScope(bool on) { g_guard = GuardState(); g_guard.on = on; }
  ~GuardScope() { g_guard.on = false; }
};
static double rel_norm(double num, double den) { return den > 0 ? num / den : (num > 0 ? R_PosInf : 0.0); }
static void guard_check(const Gram& g, const Chol& ch, const arma::vec& w, const arma::vec& Xty, const arma::vec& mu, const arma::vec& theta) {
  arma::vec At = g.G * theta + w % theta;
  arma::vec Ltt = ch.L.t() * theta;
  arma::vec e = At - ch.L * Ltt;
  double r = rel_norm(arma::norm(e), arma::norm(At));
  double rw = rel_norm(arma::norm(arma::solve(arma::trimatl(ch.L), e)), arma::norm(Ltt));
  double rmean = rel_norm(arma::norm(g.G * mu + w % mu - Xty), arma::norm(Xty));
  g_guard.r.push_back(r); g_guard.rw.push_back(rw); g_guard.rmean.push_back(rmean);
  if (!(rw <= 1e-8 && rmean <= 1e-8))
    Rcpp::stop("hs_fast (exact mode): sweep %ld: the dense factor of G + diag(1/(tau lambda)^2) is not accurate enough "
               "(backward error %.3g in the factor's metric, mean-solve residual %.3g; limit 1e-8). The design is numerically "
               "collinear and the prior precision is lost to rounding, so the exact conditional of theta cannot be computed reliably. "
               "Use Chebyshev nodes instead of an equispaced grid, or reduce / orthogonalize the columns of X.", g_guard.sweep, rw, rmean);
}

// ---------------------------------------------------------------- the four conditional updates (one sweep = in this order)
// theta | lambda, tau, s2
static arma::vec draw_theta(const Gram& g, const arma::vec& Xty, const arma::vec& lambda, double tau, double s2) {
  int p = Xty.n_elem; arma::vec z(p);
  arma::vec w = 1.0 / arma::square(tau * lambda);
  double s = std::sqrt(s2);
  for (int j = 0; j < p; ++j) z[j] = R::norm_rand();
  Chol ch = factor(g, w);
  arma::vec mu = bwd(ch, fwd(ch, Xty));
  arma::vec theta = mu + s * bwd(ch, z);           // the same arithmetic as before change (6)
  if (g_guard.on && g.type == 0) guard_check(g, ch, w, Xty, mu, theta);
  return theta;
}
// lambda | theta, tau, s2 (in place). clamp bit 1: the package floor; off: exact.
static void update_lambda(arma::vec& lambda, const arma::vec& theta, double tau, double s2, int clamp) {
  int p = theta.n_elem; arma::vec upsi(p), Fub(p), tempps(p), ub(p);
  for (int j = 0; j < p; ++j) { double eta = 1.0 / (lambda[j] * lambda[j]); upsi[j] = R::runif(0.0, 1.0 / (1.0 + eta)); }
  for (int j = 0; j < p; ++j) {
    tempps[j] = theta[j] * theta[j] / (2 * s2 * tau * tau);
    ub[j] = (1 - upsi[j]) / upsi[j];
    if (clamp & 1) { Fub[j] = 1 - std::exp(-tempps[j] * ub[j]); if (Fub[j] < 1e-4) Fub[j] = 1e-4; }
    else Fub[j] = -std::expm1(-tempps[j] * ub[j]);
  }
  if (clamp & 1) {
    for (int j = 0; j < p; ++j) Fub[j] = R::runif(0.0, Fub[j]);            // Fub now holds 'up'
    for (int j = 0; j < p; ++j) lambda[j] = 1.0 / std::sqrt(-std::log(1 - Fub[j]) / tempps[j]);
  } else {
    for (int j = 0; j < p; ++j) {
      double V = R::unif_rand(), x = tempps[j] * ub[j], eta;
      if (x < 1e-300) eta = ub[j] * V;
      else eta = -std::log1p(-(Fub[j] * V)) / tempps[j];
      lambda[j] = 1.0 / std::sqrt(eta);
    }
  }
  if (!lambda.is_finite() || arma::any(lambda <= 0)) Rcpp::stop("hs_fast: invalid lambda draw (non-finite or not positive)");
}
// tau | theta, lambda, s2 (half-Cauchy prior). clamp bit 2: the package floor; off: exact.
static double update_tau(double tau, const arma::vec& theta, const arma::vec& lambda, double s2, int clamp) {
  int p = theta.n_elem;
  double tempt = arma::sum(arma::square(theta / lambda)) / (2 * s2);
  double et = 1.0 / (tau * tau);
  double utau = R::runif(0.0, 1.0 / (1.0 + et));
  double ubt = (1 - utau) / utau, shape = (p + 1) / 2.0, scale = 1.0 / tempt;
  if (clamp & 2) {
    double Fubt = R::pgamma(ubt, shape, scale, 1, 0); if (Fubt < 1e-8) Fubt = 1e-8;
    double ut = R::runif(0.0, Fubt);
    et = R::qgamma(ut, shape, scale, 1, 0);
  } else {
    if (!(std::isfinite(ubt) && ubt > 0 && std::isfinite(tempt) && tempt >= 0))
      Rcpp::stop("hs_fast: invalid tau slice (ubt = %g, rate = %g)", ubt, tempt);
    double V = R::unif_rand();
    if (tempt * ubt < 1e-300) et = ubt * std::pow(V, 1.0 / shape);   // zero-rate limit: density prop. to et^(shape-1) on (0, ubt)
    else {
      double lF = R::pgamma(ubt, shape, scale, 1, 1);
      double lu = lF + std::log(V);
      et = R::qgamma(lu, shape, scale, 1, 1);
      if (std::isfinite(et) && et > ubt && et <= ubt * (1 + 1e-12)) et = ubt;   // round-off overshoot at the slice boundary only
    }
  }
  if (!(std::isfinite(et) && et > 0 && (clamp & 2 || et <= ubt))) Rcpp::stop("hs_fast: invalid tau draw (1/tau^2 = %g, bound %g)", et, ubt);
  return 1.0 / std::sqrt(et);
}
// s2 | theta, lambda, tau (Jeffreys prior). RSS from the residual y - X theta (as the package), plus rss_extra (Geweke pseudo-data).
// clamp bit 4: the package's floors E1, E2 >= 1e-8; off: none.
static double update_s2(const arma::mat& X, const arma::vec& y, const arma::vec& theta, const arma::vec& lambda, double tau,
                        int n, double rss_extra, int clamp) {
  int p = theta.n_elem;
  double E1 = arma::accu(arma::square(y - X * theta)) + rss_extra;
  double E2 = arma::sum(arma::square(theta / (tau * lambda)));
  if (clamp & 4) { E1 = std::max(E1, 1e-8); E2 = std::max(E2, 1e-8); }
  if (!(std::isfinite(E1 + E2) && E1 + E2 > 0)) Rcpp::stop("hs_fast: invalid sigma^2 conditional (RSS + prior term = %g)", E1 + E2);
  double s2 = 1.0 / R::rgamma((n + p) / 2.0, 2.0 / (E1 + E2));
  if (!(std::isfinite(s2) && s2 > 0)) Rcpp::stop("hs_fast: invalid sigma^2 draw (%g)", s2);
  return s2;
}
// one sweep, in the package's order (theta, lambda, tau, s2); shared with the Geweke driver
static void one_sweep(const Gram& g, const arma::mat& X, const arma::vec& y, const arma::vec& Xty, int n, double rss_extra,
                      bool tau_fixed, bool sigma_fixed, int clamp, arma::vec& theta, arma::vec& lambda, double& tau, double& s2) {
  theta = draw_theta(g, Xty, lambda, tau, s2);
  if (!theta.is_finite()) Rcpp::stop("hs_fast: non-finite theta draw");
  update_lambda(lambda, theta, tau, s2, clamp);
  if (!tau_fixed) tau = update_tau(tau, theta, lambda, s2, clamp);
  if (!sigma_fixed) s2 = update_s2(X, y, theta, lambda, tau, n, rss_extra, clamp);
}

// ---------------------------------------------------------------- the sampler
// [[Rcpp::export]]
List hsfast_kernel(const arma::mat& X, const arma::vec& y, const arma::vec& Xty, int n, List gram, bool tau_fixed, double tau0,
                   bool sigma_fixed, double s2_0, int burn, int nmc, int clamp, int nbatch = 50, int max_save = 5000, int full = 0,
                   int guard = 0) {
  Gram g = read_gram(gram);
  GuardScope gscope(guard != 0 && g.type == 0);
  int p = Xty.n_elem;
  if ((int)X.n_rows != n || (int)X.n_cols != p || (int)y.n_elem != n) Rcpp::stop("hsfast_kernel: X must be n x p and y length n");
  if (clamp < 0 || clamp > 7) Rcpp::stop("hsfast_kernel: clamp must be in 0..7");
  arma::vec theta(p, arma::fill::zeros), lambda(p, arma::fill::ones);
  double tau = tau0, s2 = s2_0;
  if (nmc % nbatch != 0) Rcpp::stop("nmc must be divisible by nbatch");
  int bsize = nmc / nbatch, thin = full ? 1 : (nmc + max_save - 1) / max_save, nsave = nmc / thin;
  arma::mat th_out(p, nsave), bm(p, nbatch, arma::fill::zeros);
  arma::vec tau_out(nsave), s2_out(nsave), bm_tau(nbatch, arma::fill::zeros), bm_s2(nbatch, arma::fill::zeros), bm_s(nbatch, arma::fill::zeros);
  arma::vec lam_sum(p, arma::fill::zeros);                       // (7) sum of lambda over the saved sweeps
  RNGScope scope;
  auto t0 = std::chrono::steady_clock::now();
  for (int it = 1; it <= burn + nmc; ++it) {
    g_guard.sweep = it;
    one_sweep(g, X, y, Xty, n, 0.0, tau_fixed, sigma_fixed, clamp, theta, lambda, tau, s2);
    if (it > burn) {
      int m = it - burn - 1, b = m / bsize;
      bm.col(b) += theta; bm_tau[b] += tau; bm_s2[b] += s2; bm_s[b] += std::sqrt(s2);
      if ((m + 1) % thin == 0 && (m + 1) / thin <= nsave) { int q = (m + 1) / thin - 1; th_out.col(q) = theta; tau_out[q] = tau; s2_out[q] = s2; lam_sum += lambda; }
    }
    if (it % 1000 == 0) Rcpp::checkUserInterrupt();
  }
  double secs = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
  bm /= (double)bsize; bm_tau /= (double)bsize; bm_s2 /= (double)bsize; bm_s /= (double)bsize;
  return List::create(_["draws"] = th_out, _["bm"] = bm, _["thin"] = thin, _["tau"] = tau_out, _["s2"] = s2_out,
                      _["bm_tau"] = bm_tau, _["bm_s2"] = bm_s2, _["bm_sigma"] = bm_s, _["seconds"] = secs, _["lambda_mean"] = lam_sum / (double)nsave,
                      _["state"] = List::create(_["lambda"] = lambda, _["tau"] = tau, _["s2"] = s2, _["theta"] = theta),
                      _["guard"] = List::create(_["on"] = g_guard.on, _["r"] = wrap(g_guard.r), _["r_w"] = wrap(g_guard.rw),
                                                _["r_mean"] = wrap(g_guard.rmean)));
}

// ---------------------------------------------------------------- helpers for checks of the linear algebra
// mu and M draws of theta ~ N(A^{-1} X'y, s2 A^{-1}) at fixed w, with the kernel's factorisation and noise map.
// [[Rcpp::export]]
List hsfast_fixed_draws(const arma::vec& Xty, List gram, const arma::vec& w, double s2, int M) {
  Gram g = read_gram(gram); int p = Xty.n_elem;
  Chol ch = factor(g, w);
  arma::vec mu = bwd(ch, fwd(ch, Xty));
  arma::mat D(p, M); arma::vec z(p); double s = std::sqrt(s2);
  RNGScope scope;
  for (int m = 0; m < M; ++m) { for (int j = 0; j < p; ++j) z[j] = R::norm_rand(); D.col(m) = mu + s * bwd(ch, z); }
  return List::create(_["mu"] = mu, _["draws"] = D);
}
// The factor itself, for checks: returns dense L (p x p) of the structured factorisation.
// [[Rcpp::export]]
arma::mat hsfast_dense_factor(List gram, const arma::vec& w) {
  Gram g = read_gram(gram); int p = w.n_elem; Chol ch = factor(g, w);
  arma::mat L(p, p, arma::fill::zeros);
  if (ch.type == 0) return ch.L;
  if (ch.type == 1) return arma::diagmat(ch.ell);
  if (ch.type == 2) { L.zeros(); for (int j = 0; j < p; ++j) for (int k = 0; k <= ch.bw && j + k < p; ++k) L(j + k, j) = ch.Lb(k, j); return L; }
  L = arma::trimatl(g.U * ch.B.t()); L.diag() = ch.ell; return L;   // strictly lower part = U B^T
}
