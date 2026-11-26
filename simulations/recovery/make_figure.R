# make_figure.R: Figure 1 of the paper (coefficient recovery, Section 3.1), drawn from coefficients.csv only (no sampling).
#   Rscript make_figure.R                         reads results/coefficients.csv (written by recovery.R)
#   Rscript make_figure.R --from=reference_outputs   reads the shipped file
# Writes figures/coef_recovery.pdf and figures/coef_recovery.png next to this script.
options(warn = 1)
here <- local({ a <- grep("^--file=", commandArgs(trailingOnly = FALSE), value = TRUE)
                if (length(a)) dirname(normalizePath(sub("^--file=", "", a[1L]))) else getwd() })
source(file.path(here, "..", "common.R"))

args <- commandArgs(trailingOnly = TRUE)
from <- sub("^--from=", "", grep("^--from=", args, value = TRUE))
from <- if (length(from) == 1L) from else "results"
if (!grepl("^(/|[A-Za-z]:)", from)) from <- file.path(here, from)
cf <- file.path(from, "coefficients.csv")
if (!file.exists(cf)) stop("not found: ", cf, " (run recovery.R first, or use --from=reference_outputs)", call. = FALSE)
d <- read.csv(cf)

J <- nrow(d); theta0 <- d$theta0; TAIL6 <- theta0[J]; tail <- 21:J
hs_mean <- d$hs_mean; lo_hs <- d$hs_lo95; hi_hs <- d$hs_hi95; b_ols <- d$ols
stopifnot(J >= 120, d$k == seq_len(J))

# ---- figure (same house style as the other figures)
# This panel() keeps the y-label 2.9 lines from the axis (the shared helper in common.R uses 2.6).
panel <- function(xlim, ylim, xat, yat, xlabels = xat, ylabels = yat, xlab = "", ylab = "") {
  plot.new(); plot.window(xlim, ylim); abline(v = xat, h = yat, col = COL$grid, lwd = 0.7)
  axis(1, at = xat, labels = xlabels, lwd = 0, col.axis = COL$axis, cex.axis = 0.85, line = -0.7)
  axis(2, at = yat, labels = ylabels, lwd = 0, col.axis = COL$axis, cex.axis = 0.85, las = 1, line = -0.7)
  if (nzchar(xlab)) mtext(xlab, side = 1, line = 1.6, col = COL$lab, cex = 0.9)
  if (nzchar(ylab)) mtext(ylab, side = 2, line = 2.9, col = COL$lab, cex = 0.9)
}
fmt <- function(v) { d <- max(0, -floor(log10(min(diff(sort(unique(v))))))); sub("^-", "−", formatC(v, format = "f", digits = d)) }
draw_coefs <- function(ks, ylim, cap, ci_lwd, pt_cex, ols_cex, xat) {
  yat <- pretty(ylim, 6); yat <- yat[yat >= ylim[1] & yat <= ylim[2]]
  panel(range(ks) + c(-0.5, 0.5) * max(1, diff(range(ks)) / 100), ylim, xat = xat, yat = yat, xlabels = xat, ylabels = fmt(yat),
        xlab = "Coefficient index k", ylab = "Coefficient value")
  points(ks, b_ols[ks], pch = 16, cex = ols_cex, col = adjustcolor(COL$alt, 0.45))
  segments(ks, lo_hs[ks], ks, hi_hs[ks], col = adjustcolor(COL$hs, 0.55), lwd = ci_lwd)
  tk <- ks[ks > 20]; if (length(tk)) segments(min(tk) - 0.5, TAIL6, max(tk) + 0.5, TAIL6, col = COL$truth, lwd = 1.2)
  bk <- ks[ks <= 20]; if (length(bk)) points(bk, theta0[bk], pch = 1, cex = pt_cex * 1.6, col = COL$truth, lwd = 1.1)
  points(ks, hs_mean[ks], pch = 16, cex = pt_cex, col = COL$hs)
  mtext(if (is.language(cap)) as.expression(cap) else cap, side = 1, line = 3.1, cex = 0.95, col = COL$lab)
}
draw6 <- function() {
  layout(matrix(c(1, 1, 2, 3), 2, byrow = TRUE), heights = c(1, 1))
  par(mar = c(4.5, 4.3, 0.6, 0.9), oma = c(0, 0, 1.9, 0), family = "sans")
  yr_all <- range(c(lo_hs, hi_hs, b_ols, theta0)); yr_all <- yr_all + c(-0.04, 0.06) * diff(yr_all)
  draw_coefs(1:J, yr_all, sprintf("(a)  All %d coefficients", J), 0.6, 0.35, 0.30, c(1, seq(100, J, 100)))
  zoom <- 1:60; yz <- range(c(lo_hs[zoom], hi_hs[zoom], b_ols[zoom], theta0[zoom])); yz <- yz + c(-0.06, 0.06) * diff(yz)
  draw_coefs(zoom, yz, "(b)  First 60 coefficients", 1.0, 0.55, 0.55, c(1, seq(10, 60, 10)))
  td <- 21:120                                                                   # tail detail: 100 coefficients, intervals readable
  yt <- max(abs(c(b_ols[td], lo_hs[td], hi_hs[td]))) * c(-1.08, 1.25)
  draw_coefs(td, yt, quote("(c)  Tail detail, " * italic(k) == 21 * ", ..., 120 (true value 0.001)"), 1.0, 0.50, 0.55, c(21, seq(40, 120, 20)))
  u <- par("usr"); lab <- sprintf("max |estimate| over all %d tail coefficients:  HS %.4f,  OLS %.4f", length(tail), max(abs(hs_mean[tail])), max(abs(b_ols[tail])))
  text(u[1] + 0.02 * diff(u[1:2]), u[4] - 0.05 * diff(u[3:4]), lab, adj = c(0, 0.5), cex = 0.72, col = "#333333")
  par(fig = c(0, 1, 0, 1), oma = c(0, 0, 0, 0), mar = c(0, 0, 0, 0), new = TRUE); plot.new()
  legend("top", horiz = TRUE, bty = "n", inset = 0.005, cex = 0.85, text.col = COL$lab, col = c(COL$truth, COL$hs, adjustcolor(COL$alt, 0.6)),
         lwd = c(NA, 1.2, NA), pch = c(1, 16, 16), pt.cex = c(1.0, 0.8, 0.8), x.intersp = 0.6,
         legend = c("True coefficient", "Horseshoe posterior mean and 95% interval", "OLS"))
}
files <- save_figure("coef_recovery", 9.0, 7.2, draw6, file.path(here, "figures"))
cat("Wrote", files, sep = "\n")
