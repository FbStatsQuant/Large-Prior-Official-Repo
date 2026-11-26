# summarize.R: from the per-fit table to Table 2 and the numbers quoted in the paper (Section 3.3; wall times of Section 3.5
# and of the appendix on exact Gibbs sampling).
#
#   Rscript summarize.R                           reads processed/fits_long.csv (written by process.R)
#   Rscript summarize.R --from=reference_outputs  reads the shipped reference_outputs/fits_long.csv
#   Rscript summarize.R --out=DIR                 writes to DIR instead of summary/
# Relative folders are taken relative to this script's folder. Base R only; it does not need the compiled sampler.
#
# Writes (into summary/; never into reference_outputs/):
#   by_n.csv             per pair and n, over the data sets: mean, sd, se, median, 10% and 90% quantiles of the design-point RMSE,
#                        the uniform-grid RMSE and the three counts; median and max MCSE/RMSE, min ESS of the fitted values,
#                        median ESS of log tau
#   results_table.csv    per pair and quantity, the least-squares slope on log n of the log of the MEAN over the data sets
#                        (estimate, se, r2, 95% interval), the slope of the log MEDIAN, and the median and quartiles of the
#                        per-data-set slopes. Quantities: raw = rate (design-point RMSE), adjusted = log mean RMSE - 0.5 log log n,
#                        raw_grid / adjusted_grid = the same on the uniform grid, gamma_q / gamma_q_rob / gamma_q_ci = the counts
#   per_seed_slopes.csv  the slope of every quantity for every data set
#   diagnostics.csv      per pair: MCSE/RMSE (median, max, share above 5%), ESS, single-chain split R-hat, total sampler wall time
#   table2.csv           the four rows of Table 2 with standard errors;  table_rows.tex  the same rows as LaTeX
#   wall_times.csv       median (min, max) wall time of a complete sampler call per pair and n
#   summary.txt          the settings and every number quoted in the text, with the paper's rounding next to the full value

options(warn = 1)
here <- local({
  a <- grep("^--file=", commandArgs(trailingOnly = FALSE), value = TRUE)
  if (length(a)) dirname(normalizePath(sub("^--file=", "", a[1L]))) else getwd()
})
in_here <- function(p) if (grepl("^(/|~|[A-Za-z]:)", p)) p else file.path(here, p)
args <- commandArgs(trailingOnly = TRUE)
opt <- function(name, default) {
  h <- grep(paste0("^--", name, "="), args, value = TRUE)
  if (length(h)) sub(paste0("^--", name, "="), "", h[length(h)]) else default
}
if (any(!grepl("^--(from|out)=", args))) stop("usage: Rscript summarize.R [--from=DIR] [--out=DIR]", call. = FALSE)
from <- in_here(opt("from", "processed")); out <- in_here(opt("out", "summary"))
f_in <- file.path(from, "fits_long.csv")
if (!file.exists(f_in)) stop("no ", f_in, " (run process.R first, or use --from=reference_outputs)", call. = FALSE)
if (dir.exists(file.path(here, "reference_outputs")) &&
    identical(normalizePath(out, mustWork = FALSE), normalizePath(file.path(here, "reference_outputs"))))
  stop("summarize.R does not write into reference_outputs/; use --out=DIR", call. = FALSE)
dir.create(out, showWarnings = FALSE, recursive = TRUE)

# The four (target, dictionary, design) pairs and noise levels: the same as CELLS and SIGMA in ../common.R (copied here so that
# this script runs without the compiled sampler). Rows in this order in results_table.csv, per_seed_slopes.csv and table2.csv.
CELLS <- data.frame(id = c("f1_fourier", "f1_bspline", "f2_chebyshev", "f2_bspline"), func = c("f1", "f1", "f2", "f2"),
                    basis = c("Fourier", "cubic B-splines", "Chebyshev", "cubic B-splines"),
                    design = c("equispaced x", "equispaced x", "Gauss-Chebyshev nodes", "Gauss-Chebyshev nodes"),
                    sigma = c(0.15, 0.15, 0.20, 0.20), stringsAsFactors = FALSE)

long <- read.csv(f_in, stringsAsFactors = FALSE)
long <- long[order(long$cell, long$seed, long$n), ]
if (!all(long$cell %in% CELLS$id)) stop("unknown pair ids in ", f_in, call. = FALSE)

# ---- per (pair, n) over the data sets: mean (the headline), sd, se = sd / sqrt(#data sets), median, 10% and 90% quantiles
qs <- c("rmse_design", "rmse_grid", "qhat", "qhat_rob", "qhat_ci")
by_n <- do.call(rbind, lapply(split(long, list(long$cell, long$n), drop = TRUE), function(d) {
  o <- data.frame(cell = d$cell[1], n = d$n[1], J = d$J[1], n_seeds = nrow(d), stringsAsFactors = FALSE)
  for (v in qs) { o[[paste0(v, "_mean")]] <- mean(d[[v]]); o[[paste0(v, "_sd")]] <- if (nrow(d) > 1L) sd(d[[v]]) else NA_real_
                  o[[paste0(v, "_se")]] <- o[[paste0(v, "_sd")]] / sqrt(nrow(d)); o[[paste0(v, "_median")]] <- median(d[[v]]); o[[paste0(v, "_q10")]] <- unname(quantile(d[[v]], 0.10, type = 7)); o[[paste0(v, "_q90")]] <- unname(quantile(d[[v]], 0.90, type = 7)) }
  o$mcse_rel_median <- median(d$mcse_rel); o$mcse_rel_max <- max(d$mcse_rel); o$ess_f_min <- min(d$ess_f_min); o$ess_logtau_median <- median(d$ess_logtau); o }))
by_n <- by_n[order(by_n$cell, by_n$n), ]; rownames(by_n) <- NULL
write.csv(by_n, file.path(out, "by_n.csv"), row.names = FALSE)

# ---- slopes: least squares on log n; NA when a value is <= 0 (log undefined) or there are fewer than 2 distinct n.
#      estimate = slope of log(mean over data sets) (the headline); median_slope = slope of log(median); per-data-set slopes.
ols <- function(y, ln) { ok <- is.finite(y); if (!all(ok) || length(unique(ln)) < 2L) return(c(est = NA, se = NA, r2 = NA))
  m <- lm(y ~ ln); sm <- suppressWarnings(summary(m)); s <- sm$coefficients; c(est = s[2, 1], se = if (nrow(s) == 2L && length(ln) > 2L) s[2, 2] else NA, r2 = sm$r.squared) }
lg <- function(v) ifelse(v > 0, log(v), NA_real_)
defs <- list(raw = list(of = "RMSE_design", v = "rmse_design", adj = FALSE), adjusted = list(of = "RMSE_design", v = "rmse_design", adj = TRUE),
             raw_grid = list(of = "RMSE_grid", v = "rmse_grid", adj = FALSE), adjusted_grid = list(of = "RMSE_grid", v = "rmse_grid", adj = TRUE),
             gamma_q = list(of = "q_hat", v = "qhat", adj = FALSE), gamma_q_rob = list(of = "q_rob", v = "qhat_rob", adj = FALSE),
             gamma_q_ci = list(of = "q_CI", v = "qhat_ci", adj = FALSE))
rows <- list(); seed_rows <- list()
for (cid in CELLS$id) {
  bn <- by_n[by_n$cell == cid, ]; if (!nrow(bn)) next
  ln <- log(bn$n)
  for (qn in names(defs)) {
    d <- defs[[qn]]; adj <- if (d$adj) 0.5 * log(log(bn$n)) else 0
    e <- ols(lg(bn[[paste0(d$v, "_mean")]]) - adj, ln); em <- ols(lg(bn[[paste0(d$v, "_median")]]) - adj, ln)
    ps <- vapply(split(long[long$cell == cid, ], long$seed[long$cell == cid]), function(dd) { dd <- dd[order(dd$n), ]; yy <- lg(dd[[d$v]]); if (d$adj) yy <- yy - 0.5 * log(log(dd$n)); ols(yy, log(dd$n))[["est"]] }, 0)
    seed_rows[[length(seed_rows) + 1L]] <- data.frame(cell = cid, quantity = qn, of = d$of, seed = as.integer(names(ps)), slope = unname(ps), stringsAsFactors = FALSE)
    fin <- ps[is.finite(ps)]
    rows[[length(rows) + 1L]] <- data.frame(cell = cid, quantity = qn, of = d$of, estimate = e[["est"]], se = e[["se"]], r2 = e[["r2"]],
      ci95_lo = e[["est"]] - qt(0.975, max(1, nrow(bn) - 2)) * e[["se"]], ci95_hi = e[["est"]] + qt(0.975, max(1, nrow(bn) - 2)) * e[["se"]],
      n_values = nrow(bn), n_seeds = min(bn$n_seeds), median_slope = em[["est"]], median_slope_se = em[["se"]],
      per_seed_median = if (length(fin)) median(fin) else NA, per_seed_q25 = if (length(fin)) unname(quantile(fin, 0.25)) else NA,
      per_seed_q75 = if (length(fin)) unname(quantile(fin, 0.75)) else NA, per_seed_n_finite = length(fin), stringsAsFactors = FALSE)
  }
}
rt <- do.call(rbind, rows); write.csv(rt, file.path(out, "results_table.csv"), row.names = FALSE)
write.csv(do.call(rbind, seed_rows), file.path(out, "per_seed_slopes.csv"), row.names = FALSE)
dg <- do.call(rbind, lapply(split(long, long$cell), function(d) data.frame(cell = d$cell[1], fits = nrow(d), mcse_rel_median = median(d$mcse_rel), mcse_rel_max = max(d$mcse_rel),
  frac_mcse_rel_over_5pct = mean(d$mcse_rel > 0.05), ess_f_min = min(d$ess_f_min), ess_f_median = median(d$ess_f_min), ess_logtau_median = median(d$ess_logtau),
  rhat1_f_max = max(d$rhat1_f_max), wall_s_total = sum(d$hs_fast_wall_s))))
write.csv(dg, file.path(out, "diagnostics.csv"), row.names = FALSE)

# ---- Table 2
get_rt <- function(cid, qty, what) { v <- rt[rt$cell == cid & rt$quantity == qty, what]; if (length(v) != 1L) stop(sprintf("results_table: %s %s not unique", cid, qty), call. = FALSE); v }
cells_in <- CELLS[CELLS$id %in% rt$cell, ]
tab2 <- do.call(rbind, lapply(seq_len(nrow(cells_in)), function(i) { cid <- cells_in$id[i]
  data.frame(func = cells_in$func[i], basis = cells_in$basis[i], design = cells_in$design[i], cell = cid,
             rate = get_rt(cid, "raw", "estimate"), rate_se = get_rt(cid, "raw", "se"), rate_r2 = get_rt(cid, "raw", "r2"),
             adjusted_rate = get_rt(cid, "adjusted", "estimate"), adjusted_rate_se = get_rt(cid, "adjusted", "se"), adjusted_rate_r2 = get_rt(cid, "adjusted", "r2"),
             gamma_q = get_rt(cid, "gamma_q", "estimate"), gamma_q_se = get_rt(cid, "gamma_q", "se"),
             gamma_q_rob = get_rt(cid, "gamma_q_rob", "estimate"), gamma_q_rob_se = get_rt(cid, "gamma_q_rob", "se"),
             gamma_q_ci = get_rt(cid, "gamma_q_ci", "estimate"), gamma_q_ci_se = get_rt(cid, "gamma_q_ci", "se"),
             n_values = get_rt(cid, "raw", "n_values"), n_seeds = get_rt(cid, "raw", "n_seeds"), stringsAsFactors = FALSE) }))
write.csv(tab2, file.path(out, "table2.csv"), row.names = FALSE)
f3 <- function(x) ifelse(is.na(x), "NA", formatC(x, format = "f", digits = 3))
tex_label <- c(f1_fourier = "Fourier", f1_bspline = "B-spline", f2_chebyshev = "Chebyshev", f2_bspline = "B-spline")
tex <- "% Rows of Table 2 (tab:convergence), paper Section 3.3; written by summarize.R"
for (fn in c("f1", "f2")) {
  r <- tab2[tab2$func == fn, ]; if (!nrow(r)) next
  if (fn == "f2" && length(tex) > 1L) tex <- c(tex, "\\midrule")
  tex <- c(tex, sprintf("\\multirow{2}{*}{$f_%s$ ($\\alpha=%d$)}", substring(fn, 2), c(f1 = 1L, f2 = 3L)[[fn]]),
           sprintf("& %-9s & $%s$ & $%s$ & $%s$ & $%s$ \\\\", tex_label[r$cell], f3(r$rate), f3(r$gamma_q), f3(r$gamma_q_rob), f3(r$gamma_q_ci)))
}
writeLines(tex, file.path(out, "table_rows.tex"))

# ---- wall time of a complete sampler call (setup, sweeps and posterior summaries), per pair and n
wt <- do.call(rbind, lapply(split(long, list(long$cell, long$n), drop = TRUE), function(d)
  data.frame(cell = d$cell[1], n = d$n[1], J = d$J[1], fits = nrow(d), wall_s_median = median(d$hs_fast_wall_s),
             wall_s_min = min(d$hs_fast_wall_s), wall_s_max = max(d$hs_fast_wall_s), stringsAsFactors = FALSE)))
wt <- wt[order(match(wt$cell, CELLS$id), wt$n), ]; rownames(wt) <- NULL
write.csv(wt, file.path(out, "wall_times.csv"), row.names = FALSE)

# ---- summary.txt: every number quoted in the text. Each line: what it is, the value with the paper's rounding, the full value.
ns <- sort(unique(long$n)); n_lo <- min(ns); n_hi <- max(ns)
complete <- length(ns) == 39L && nrow(long) == 15600L && all(by_n$n_seeds == 100L) && setequal(unique(long$cell), CELLS$id)
B <- function(cid, n, col) { v <- by_n[by_n$cell == cid & by_n$n == n, col]; if (length(v) == 1L) v else NA_real_ }
R <- function(cid, qty, col = "estimate") { v <- rt[rt$cell == cid & rt$quantity == qty, col]; if (length(v) == 1L) v else NA_real_ }
D <- function(cid, col) { v <- dg[dg$cell == cid, col]; if (length(v) == 1L) v else NA_real_ }
W <- function(cid, n) { v <- wt$wall_s_median[wt$cell == cid & wt$n == n]; if (length(v) == 1L) v else NA_real_ }
full <- function(x) ifelse(is.na(x), "n/a", trimws(formatC(x, digits = 15, format = "g")))
rnd <- function(x, d) ifelse(is.na(x), "n/a", formatC(x, format = "f", digits = d))
txt <- character(0)
say <- function(...) txt <<- c(txt, sprintf(...))
num <- function(label, x, d, scale = 1, unit = "") say("  %-74s %9s%s   (full value %s)", label, rnd(scale * x, d), unit, full(x))
rng <- function(label, x, d, scale = 1, unit = "") say("  %-74s %s%s to %s%s   (full values %s and %s)", label, rnd(scale * min(x), d), unit,
                                                         rnd(scale * max(x), d), unit, full(min(x)), full(max(x)))
G <- c("f1_fourier", "f2_chebyshev"); S <- c("f1_bspline", "f2_bspline")
nm <- c(f1_fourier = "f1, Fourier", f1_bspline = "f1, B-splines", f2_chebyshev = "f2, Chebyshev", f2_bspline = "f2, B-splines")

say("Scaling experiment, paper Section 3.3 (Table 2, Figure 3); wall times of Section 3.5 and of the appendix on exact Gibbs sampling")
say("Input: %s (%d fits)", file.path(basename(from), "fits_long.csv"), nrow(long))
say("Design: f1 with the Fourier dictionary and cubic B-splines (equispaced x); f2 with the Chebyshev dictionary and cubic B-splines")
say("  (Gauss-Chebyshev nodes); n = %s (%d values), J = floor(n^0.7) from %d to %d; %d data sets per n; one chain per fit.",
    if (identical(as.integer(ns), as.integer(seq(1000, 20000, 500)))) "1000, 1500, ..., 20000" else paste(ns, collapse = ", "), length(ns),
    min(long$J), max(long$J), min(by_n$n_seeds))
say("Complete run (39 n x 100 data sets x 4 pairs): %s", if (complete) "yes" else "NO - partial input; numbers below use what is there")
say("Rates and gammas are least-squares slopes on log n of the log of the mean over the data sets. Values are rounded as in the paper.")
say("")
say("Table 2 (3 decimals; standard errors in table2.csv)")
for (cid in CELLS$id) {
  num(sprintf("%s: rate", nm[[cid]]), R(cid, "raw"), 3)
  num(sprintf("%s: gamma_q", nm[[cid]]), R(cid, "gamma_q"), 3)
  num(sprintf("%s: gamma_q^rob", nm[[cid]]), R(cid, "gamma_q_rob"), 3)
  num(sprintf("%s: gamma_q^CI", nm[[cid]]), R(cid, "gamma_q_ci"), 3)
}
tse <- rt$se[rt$quantity %in% c("raw", "gamma_q", "gamma_q_rob", "gamma_q_ci")]
num("Largest least-squares standard error of the 16 slopes of Table 2", max(tse), 4)
num("Largest least-squares standard error of all slopes in results_table.csv", max(rt$se), 4)
say("")
say("Section 3.3, Results")
num("Rate ratio, global dictionary / B-splines, f1", R("f1_fourier", "raw") / R("f1_bspline", "raw"), 1)
num("Rate ratio, global dictionary / B-splines, f2", R("f2_chebyshev", "raw") / R("f2_bspline", "raw"), 1)
for (cid in CELLS$id) {
  num(sprintf("Mean RMSE at n = %d, %s", n_lo, nm[[cid]]), B(cid, n_lo, "rmse_design_mean"), 4)
  num(sprintf("Mean RMSE at n = %d, %s", n_hi, nm[[cid]]), B(cid, n_hi, "rmse_design_mean"), 4)
}
num(sprintf("Mean RMSE ratio B-splines / Fourier at n = %d, f1", n_hi), B("f1_bspline", n_hi, "rmse_design_mean") / B("f1_fourier", n_hi, "rmse_design_mean"), 1)
num(sprintf("Mean RMSE ratio B-splines / Chebyshev at n = %d, f2", n_hi), B("f2_bspline", n_hi, "rmse_design_mean") / B("f2_chebyshev", n_hi, "rmse_design_mean"), 1)
num("-(1 - b)/2 with b = 0.7 (variance of about J_n active coefficients)", -(1 - 0.7) / 2, 2)
dev <- c()
for (cid in S) for (n in c(n_lo, n_hi)) {
  sg <- CELLS$sigma[CELLS$id == cid]; J <- by_n$J[by_n$cell == cid & by_n$n == n]
  if (!length(J)) next
  r <- B(cid, n, "rmse_design_mean") / (sg * sqrt(J / n)); dev <- c(dev, abs(r - 1))
  num(sprintf("Mean RMSE / (sigma sqrt(J_n/n)) at n = %d, %s", n, nm[[cid]]), r, 3)
}
if (length(dev)) num("  largest |ratio - 1| over these four, in %", max(dev), 1, 100, "%")
for (cid in CELLS$id) {
  num(sprintf("Per-data-set rate, lower quartile, %s", nm[[cid]]), R(cid, "raw", "per_seed_q25"), 3)
  num(sprintf("Per-data-set rate, upper quartile, %s", nm[[cid]]), R(cid, "raw", "per_seed_q75"), 3)
}
dmed <- sapply(CELLS$id, function(cid) abs(R(cid, "raw", "median_slope") - R(cid, "raw")))
for (cid in CELLS$id) num(sprintf("|slope of median RMSE - slope of mean RMSE|, %s", nm[[cid]]), dmed[[cid]], 4)
num("  largest of the four", max(dmed), 3)
dgr <- c(sapply(CELLS$id, function(cid) abs(R(cid, "raw_grid") - R(cid, "raw"))), sapply(CELLS$id, function(cid) abs(R(cid, "adjusted_grid") - R(cid, "adjusted"))))
for (cid in CELLS$id) num(sprintf("|rate on the uniform grid - rate at the design points|, %s", nm[[cid]]), abs(R(cid, "raw_grid") - R(cid, "raw")), 4)
num("  largest change of any slope (rate and adjusted rate, four pairs)", max(dgr), 3)
num("MCSE of the fitted values / RMSE, largest over all fits, in %", max(long$mcse_rel), 1, 100, "%")
for (cid in CELLS$id) num(sprintf("MCSE / RMSE, median over the fits, %s, in %%", nm[[cid]]), D(cid, "mcse_rel_median"), 1, 100, "%")
num("Largest inflation of the RMSE by MC error, sqrt(1+(MCSE/RMSE)^2) - 1, in %", sqrt(1 + max(long$mcse_rel)^2) - 1, 2, 100, "%")
for (cid in CELLS$id) num(sprintf("Median effective sample size of log tau, %s", nm[[cid]]), D(cid, "ess_logtau_median"), 0)
say("")
say("Section 3.3, coefficient counts")
num(sprintf("Growth of J_n over the grid, J(%d) / J(%d)", n_hi, n_lo), max(long$J) / min(long$J), 2)
for (cid in CELLS$id) {
  num(sprintf("Mean number of credibly non-zero coefficients at n = %d, %s", n_lo, nm[[cid]]), B(cid, n_lo, "qhat_ci_mean"), 1)
  num(sprintf("Mean number of credibly non-zero coefficients at n = %d, %s", n_hi, nm[[cid]]), B(cid, n_hi, "qhat_ci_mean"), 1)
}
rng("Mean credibly non-zero count over the whole grid, f2, Chebyshev", by_n$qhat_ci_mean[by_n$cell == "f2_chebyshev"], 1)
rng("gamma_q^rob and gamma_q^CI, global dictionaries", sapply(G, function(cid) c(R(cid, "gamma_q_rob"), R(cid, "gamma_q_ci"))), 2)
rng("gamma_q^rob and gamma_q^CI, B-splines", sapply(S, function(cid) c(R(cid, "gamma_q_rob"), R(cid, "gamma_q_ci"))), 2)
rng(sprintf("Share of credibly non-zero B-spline coefficients at n = %d, in %%", n_lo), sapply(S, function(cid) B(cid, n_lo, "qhat_ci_mean") / B(cid, n_lo, "J")), 0, 100, "%")
rng(sprintf("Share of credibly non-zero B-spline coefficients at n = %d, in %%", n_hi), sapply(S, function(cid) B(cid, n_hi, "qhat_ci_mean") / B(cid, n_hi, "J")), 0, 100, "%")
for (cid in S) num(sprintf("gamma_q (threshold 1/J_n), %s", nm[[cid]]), R(cid, "gamma_q"), 3)
for (cid in S) {
  num(sprintf("Mean count with threshold 1/J_n at n = %d, %s (J = %d)", n_lo, nm[[cid]], min(long$J)), B(cid, n_lo, "qhat_mean"), 2)
  num(sprintf("Mean count with threshold 1/J_n at n = %d, %s (J = %d)", n_hi, nm[[cid]], max(long$J)), B(cid, n_hi, "qhat_mean"), 2)
}
rng("gamma_q^CI, global dictionaries", sapply(G, R, qty = "gamma_q_ci"), 2)
rng("Rate, global dictionaries", sapply(G, R, qty = "raw"), 2)
rng("gamma_q^CI, B-splines", sapply(S, R, qty = "gamma_q_ci"), 2)
rng("Rate, B-splines", sapply(S, R, qty = "raw"), 2)
num("Rate f1, Fourier, minus (-3/8)", R("f1_fourier", "raw") + 3 / 8, 3)
say("")
say("Wall time of a complete sampler call (setup, all sweeps and posterior summaries; 7,000 sweeps in the paper run), median over the data sets")
for (n in intersect(c(1000L, 10000L, 20000L), ns)) {
  w <- sapply(CELLS$id, W, n = n)
  for (cid in CELLS$id) num(sprintf("n = %d (J = %d), %s, seconds", n, by_n$J[by_n$n == n][1], nm[[cid]]), w[[cid]], 2)
  rng(sprintf("  range over the four pairs at n = %d, seconds", n), w, 2)
}
writeLines(txt, file.path(out, "summary.txt"))
cat(txt, sep = "\n")
cat(sprintf("\nwrote by_n.csv, results_table.csv, per_seed_slopes.csv, diagnostics.csv, table2.csv, table_rows.tex, wall_times.csv, summary.txt to %s\n", out))
