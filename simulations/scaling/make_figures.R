# make_figures.R: Figure 3 of the paper (Section 3.3), one file per panel: figures/scaling_f1.{pdf,png} and scaling_f2.{pdf,png}.
# Mean RMSE against n on log-log axes: points = means over the data sets with +-2 standard errors, band = 10% to 90% quantiles over
# the data sets, line = least-squares fit of log mean RMSE on log n; the legend gives the rate of Table 2.
#
#   Rscript make_figures.R                            reads summary/by_n.csv and summary/results_table.csv (from summarize.R)
#   Rscript make_figures.R --from=reference_outputs   reads the shipped ones
# Relative folders are taken relative to this script's folder. Base R graphics with cairo (vector PDF, 300-dpi PNG); it does not
# need the compiled sampler. The rate is recomputed from by_n.csv and must equal results_table.csv.

options(warn = 1)
here <- local({
  a <- grep("^--file=", commandArgs(trailingOnly = FALSE), value = TRUE)
  if (length(a)) dirname(normalizePath(sub("^--file=", "", a[1L]))) else getwd()
})
in_here <- function(p) if (grepl("^(/|~|[A-Za-z]:)", p)) p else file.path(here, p)
args <- commandArgs(trailingOnly = TRUE)
if (any(!grepl("^--from=", args))) stop("usage: Rscript make_figures.R [--from=DIR]", call. = FALSE)
from <- in_here(if (length(args)) sub("^--from=", "", args[length(args)]) else "summary")
out <- file.path(here, "figures")
for (f in c("by_n.csv", "results_table.csv")) if (!file.exists(file.path(from, f))) stop("no ", file.path(from, f), " (run summarize.R first)", call. = FALSE)

# Figure style: the same as the helpers COL, mns(), panel() and save_figure() in ../common.R, copied here so that this script runs
# without the compiled sampler.
COL <- list(grid = "#E6E6E6", axis = "#4D4D4D", lab = "#222222", truth = "#1A1A1A", hs = "#2457A6", alt = "#D17A22")
mns <- function(v, d = 3) sub("^-", "−", formatC(v, format = "f", digits = d))      # typographic minus
panel <- function(xlim, ylim, xat, yat, xlab_at = xat, ylab_at = yat, xlabels = xlab_at, ylabels = ylab_at, xlab = "", ylab = "", log = "") {
  plot.new(); plot.window(xlim, ylim, log = log)
  abline(v = xat, h = yat, col = COL$grid, lwd = 0.7)
  axis(1, at = xlab_at, labels = xlabels, lwd = 0, col.axis = COL$axis, cex.axis = 0.85, line = -0.7)
  axis(2, at = ylab_at, labels = ylabels, lwd = 0, col.axis = COL$axis, cex.axis = 0.85, las = 1, line = -0.7)
  if (nzchar(xlab)) mtext(xlab, side = 1, line = 1.6, col = COL$lab, cex = 0.9)
  if (nzchar(ylab)) mtext(ylab, side = 2, line = 2.6, col = COL$lab, cex = 0.9)
}
save_figure <- function(stem, w, h, draw, dir) {
  if (!isTRUE(capabilities("cairo")))
    stop("save_figure: this R build has no cairo support (needed for the vector PDF with UTF-8 glyphs and the 300-dpi PNG)", call. = FALSE)
  dir.create(dir, showWarnings = FALSE, recursive = TRUE)
  grDevices::cairo_pdf(file.path(dir, paste0(stem, ".pdf")), width = w, height = h, family = "sans"); draw(); dev.off()
  png(file.path(dir, paste0(stem, ".png")), width = round(w * 300), height = round(h * 300), res = 300, type = "cairo", family = "sans"); draw(); dev.off()
  invisible(file.path(dir, paste0(stem, c(".pdf", ".png"))))
}

byn <- read.csv(file.path(from, "by_n.csv"), stringsAsFactors = FALSE)
rt <- read.csv(file.path(from, "results_table.csv"), stringsAsFactors = FALSE)
cells <- data.frame(cell = c("f1_fourier", "f1_bspline", "f2_chebyshev", "f2_bspline"), func = c("f1", "f1", "f2", "f2"),
                    basis = c("Fourier", "cubic B-splines", "Chebyshev", "cubic B-splines"),
                    col = c(COL$hs, COL$alt, COL$hs, COL$alt), pch = c(16, 17, 16, 17), stringsAsFactors = FALSE)
get_rt <- function(cid, qty, what) { v <- rt[rt$cell == cid & rt$quantity == qty, what]; if (length(v) != 1L) stop(sprintf("results_table: %s %s not unique", cid, qty), call. = FALSE); v }
fits <- lapply(cells$cell, function(cid) {
  d <- byn[byn$cell == cid, ]; d <- d[order(d$n), ]
  if (nrow(d) < 2L) stop(sprintf("by_n: %s has fewer than 2 sample sizes", cid), call. = FALSE)
  if (nrow(d) != 39L || any(d$n_seeds != 100L)) message(sprintf("note: %s has %d sample sizes and %d-%d data sets per n (the paper: 39 and 100)",
                                                                cid, nrow(d), min(d$n_seeds), max(d$n_seeds)))
  cf <- coef(lm(log(d$rmse_design_mean) ~ log(d$n)))
  if (abs(cf[[2]] - get_rt(cid, "raw", "estimate")) > 1e-10)
    stop(sprintf("%s: recomputed rate %.15g differs from results_table %.15g", cid, cf[[2]], get_rt(cid, "raw", "estimate")), call. = FALSE)
  list(d = d, icpt = cf[[1]], slope = cf[[2]])
}); names(fits) <- cells$cell

ns <- sort(unique(byn$n)); xat <- c(1000, 2000, 5000, 10000, 20000)
draw_panel <- function(fn, caption) {
  cs <- cells[cells$func == fn, ]
  lo <- unlist(lapply(cs$cell, function(cid) { d <- fits[[cid]]$d; c(d$rmse_design_q10, pmax(d$rmse_design_mean - 2 * d$rmse_design_se, 1e-9)) }))
  hi <- unlist(lapply(cs$cell, function(cid) { d <- fits[[cid]]$d; c(d$rmse_design_q90, d$rmse_design_mean + 2 * d$rmse_design_se) }))
  yr <- range(lo, hi); yr <- exp(log(yr) + c(-0.05, 0.22) * diff(log(yr)))
  yat <- c(outer(c(1, 2, 5), 10^(-4:0))); yat <- yat[yat >= yr[1] & yat <= yr[2]]
  if (length(yat) < 3L) { yat <- c(outer(c(1, 1.5, 2, 3, 5, 7), 10^(-4:0))); yat <- yat[yat >= yr[1] & yat <= yr[2]] }
  panel(range(ns) * c(0.93, 1.05), yr, xat = xat, yat = yat, xlabels = formatC(xat, format = "d", big.mark = ","), ylabels = format(yat, scientific = FALSE, drop0trailing = TRUE),
        xlab = "n (log scale)", ylab = "Mean RMSE (log scale)", log = "xy")
  for (k in seq_len(nrow(cs))) {
    d <- fits[[cs$cell[k]]]$d; cc <- cs$col[k]
    polygon(c(d$n, rev(d$n)), c(d$rmse_design_q10, rev(d$rmse_design_q90)), col = adjustcolor(cc, 0.13), border = NA)
    l <- pmax(d$rmse_design_mean - 2 * d$rmse_design_se, 1e-9); h <- d$rmse_design_mean + 2 * d$rmse_design_se
    segments(d$n, l, d$n, h, col = cc, lwd = 0.9)
    lines(range(ns), exp(fits[[cs$cell[k]]]$icpt + fits[[cs$cell[k]]]$slope * log(range(ns))), col = cc, lwd = 1.6)
    points(d$n, d$rmse_design_mean, pch = cs$pch[k], col = cc, cex = 0.7)
  }
  leg <- vapply(seq_len(nrow(cs)), function(k) sprintf("%s: rate %s", cs$basis[k], mns(get_rt(cs$cell[k], "raw", "estimate"))), "")
  legend("topright", bty = "o", bg = adjustcolor("white", 0.85), box.col = NA, cex = 0.78, text.col = COL$lab, col = cs$col, pch = cs$pch, lwd = 1.6,
         pt.cex = 0.8, legend = leg, inset = c(0.01, 0.02))
  mtext(caption, side = 1, line = 3.0, cex = 1.0, col = COL$lab)
}
caps <- list(f1 = quote("(a)  " * italic(f)[1] * ": Fourier vs cubic B-splines (equispaced x)"),
             f2 = quote("(b)  " * italic(f)[2] * ": Chebyshev vs cubic B-splines (Gauss-Chebyshev nodes)"))
for (fn in c("f1", "f2")) save_figure(paste0("scaling_", fn), 6.4, 4.6, function() {
  par(mar = c(4.6, 4.3, 0.8, 0.9), oma = c(0, 0, 0, 0), family = "sans"); draw_panel(fn, as.expression(caps[[fn]])) }, out)
cat(sprintf("wrote scaling_f1.{pdf,png} and scaling_f2.{pdf,png} to %s; rates %s\n", out,
            paste(sprintf("%s %s", cells$cell, vapply(cells$cell, function(cid) formatC(get_rt(cid, "raw", "estimate"), format = "f", digits = 3), "")), collapse = ", ")))
