// geweke_driver.cpp: test code for check_geweke.R (not part of the sampler). check_geweke.R compiles the text of ../hs_fast.cpp
// FOLLOWED BY this file as one translation unit, so the blocks below call the sampler's own functions draw_theta, update_lambda,
// update_tau, update_s2 and one_sweep directly.
//
// Joint-distribution test in the sense of Geweke (2004), restart form with a paired statistic. Replicate r = 1..M independently:
//   prior   : lambda_j ~ C+(0,1); tau ~ C+(0,1) (or fixed); sigma^2 ~ IG(m0/2, S0/2) (or fixed); theta_j ~ N(0, sigma^2 tau^2 lambda_j^2)
//   data    : y = X theta + sigma e
//   h0      = h(state, y);  apply one block (or nsweep full sweeps);  h1 = h(state', y)
// A correct block leaves the joint distribution of (state, y) invariant, so E(h1 - h0) = 0 and z = mean(d) / (sd(d) / sqrt(M)),
// d = h1 - h0, is approximately N(0, 1).
// Proper prior on sigma^2 with the sampler's own Jeffreys update: m0 pseudo-observations with zero design rows and sum of squares
// S0 (n -> n + m0, RSS -> RSS + S0, the update's argument rss_extra) turn the Jeffreys conditional IG((n+p)/2, (RSS+E2)/2) into
// IG((n+m0+p)/2, (RSS+S0+E2)/2), the exact conditional under the proper prior sigma^2 ~ IG(m0/2, S0/2). The sampler is unchanged.
// Blocks: 0 full sweep = the sampler's one_sweep() (theta, lambda, tau, s2), 1 theta, 2 lambda, 3 tau, 4 s2.
// Test functions (K = 6p + 6), bounded or with all moments under the horseshoe prior: per k, with sk = sigma / sqrt(G_kk),
//   a = atan(theta_k / sk), a^2, l = log lambda_k, l^2, a * atan(c_k / (sigma sqrt(G_kk))) [c = X'y], a^2 * l;
//   then log tau, (log tau)^2, log s2, (log s2)^2, log tau * log s2, log tau * mean(l).

static void gw_h(arma::vec& h, const arma::vec& theta, const arma::vec& lambda, double tau, double s2, const arma::vec& Xty, const arma::vec& Gd) {
  int p = theta.n_elem; double s = std::sqrt(s2), ml = 0;
  for (int k = 0; k < p; ++k) {
    double sk = s / std::sqrt(Gd[k]), a = std::atan(theta[k] / sk), l = std::log(lambda[k]);
    double cc = std::atan(Xty[k] / (s * std::sqrt(Gd[k])));
    h[6 * k] = a; h[6 * k + 1] = a * a; h[6 * k + 2] = l; h[6 * k + 3] = l * l; h[6 * k + 4] = a * cc; h[6 * k + 5] = a * a * l; ml += l;
  }
  ml /= p; double lt = std::log(tau), ls = std::log(s2); int o = 6 * p;
  h[o] = lt; h[o + 1] = lt * lt; h[o + 2] = ls; h[o + 3] = ls * ls; h[o + 4] = lt * ls; h[o + 5] = lt * ml;
}

// [[Rcpp::export]]
List gw_restart(List gram, const arma::mat& X, int block, int M, bool tau_fixed, double tau_fix, bool sigma_fixed, double s2_fix,
                int m0, double S0, int clamp, int nsweep) {
  Gram g = read_gram(gram); int n = X.n_rows, p = X.n_cols, K = 6 * p + 6;
  arma::vec Gd = arma::sum(arma::square(X), 0).t();
  arma::vec h0(K), h1(K), sd(K, arma::fill::zeros), sd2(K, arma::fill::zeros), sh0(K, arma::fill::zeros);
  arma::vec lambda(p), theta(p), y(n), e(n);
  long long nonfinite = 0;
  for (int r = 0; r < M; ++r) {
    for (int j = 0; j < p; ++j) lambda[j] = std::fabs(R::rcauchy(0.0, 1.0));
    double tau = tau_fixed ? tau_fix : std::fabs(R::rcauchy(0.0, 1.0));
    double s2 = sigma_fixed ? s2_fix : 1.0 / R::rgamma(m0 / 2.0, 2.0 / S0);
    double s = std::sqrt(s2);
    for (int j = 0; j < p; ++j) theta[j] = s * tau * lambda[j] * R::norm_rand();
    for (int i = 0; i < n; ++i) e[i] = R::norm_rand();
    y = X * theta + s * e;
    arma::vec Xty = X.t() * y;
    double extra = sigma_fixed ? 0.0 : S0;                   // pseudo-observations: n -> n + m0, RSS -> RSS + S0
    int nn = n + (sigma_fixed ? 0 : m0);
    gw_h(h0, theta, lambda, tau, s2, Xty, Gd);
    for (int sw = 0; sw < nsweep; ++sw) {
      if (block == 0) { one_sweep(g, X, y, Xty, nn, extra, tau_fixed, sigma_fixed, clamp, theta, lambda, tau, s2); continue; }   // the sampler's own sweep
      if (block == 1) theta = draw_theta(g, Xty, lambda, tau, s2);
      if (block == 2) update_lambda(lambda, theta, tau, s2, clamp);
      if (block == 3 && !tau_fixed) tau = update_tau(tau, theta, lambda, s2, clamp);
      if (block == 4 && !sigma_fixed) s2 = update_s2(X, y, theta, lambda, tau, nn, extra, clamp);
    }
    gw_h(h1, theta, lambda, tau, s2, Xty, Gd);
    arma::vec d = h1 - h0;
    if (!d.is_finite()) { ++nonfinite; continue; }
    sd += d; sd2 += arma::square(d); sh0 += h0;
    if (r % 10000 == 0) Rcpp::checkUserInterrupt();
  }
  double Mf = (double)(M - nonfinite);
  arma::vec mean_d = sd / Mf, var_d = sd2 / Mf - arma::square(mean_d);
  return List::create(_["mean_d"] = mean_d, _["sd_d"] = arma::sqrt(arma::clamp(var_d, 0.0, arma::datum::inf) * Mf / (Mf - 1)),
                      _["mean_h0"] = sh0 / Mf, _["M"] = Mf, _["nonfinite"] = (double)nonfinite);
}
