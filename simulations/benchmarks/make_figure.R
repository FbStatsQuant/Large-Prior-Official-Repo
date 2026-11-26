# make_figure.R: Figure 2 of the paper (Horseshoe fits at J = floor(n^0.7) = 125, Section 3.2), drawn from saved CSVs only (no sampling).
#   Rscript make_figure.R                            reads results/display_points.csv and results/display_metrics.csv (from benchmarks.R)
#   Rscript make_figure.R --from=reference_outputs   reads the shipped files
# Writes figures/hs_fits.pdf and figures/hs_fits.png next to this script.
options(warn = 1)
here <- local({ a <- grep("^--file=", commandArgs(trailingOnly = FALSE), value = TRUE)
                if (length(a)) dirname(normalizePath(sub("^--file=", "", a[1L]))) else getwd() })
source(file.path(here, "..", "common.R"))

args <- commandArgs(trailingOnly = TRUE)
from <- sub("^--from=", "", grep("^--from=", args, value = TRUE))
from <- if (length(from) == 1L) from else "results"
if (!grepl("^(/|[A-Za-z]:)", from)) from <- file.path(here, from)
pf <- file.path(from, "display_points.csv"); mf <- file.path(from, "display_metrics.csv")
if (!all(file.exists(c(pf, mf)))) stop("not found: display_points.csv / display_metrics.csv in ", from, " (run benchmarks.R first, or use --from=reference_outputs)", call. = FALSE)
pts <- read.csv(pf); met <- read.csv(mf)
PANELS <- c("a", "b"); stopifnot(all(PANELS %in% pts$panel), all(PANELS %in% met$panel))
dd <- lapply(PANELS, function(p) { d <- pts[pts$panel == p, ]; list(x = d$x, f0 = d$truth, fitted = d$fitted, mse_x1000 = met$mse_x1000[met$panel == p]) })
names(dd) <- PANELS

# ---- figure: true function and Horseshoe posterior mean, n = 1000, J = 125
caps <- list(a = quote("(a)  " * italic(f)[1] * ", Fourier"), b = quote("(b)  " * italic(f)[2] * ", Chebyshev"))
draw31 <- function() {
  par(mfrow = c(1, 2), mar = c(4.4, 3.9, 0.6, 0.9), oma = c(0, 0, 1.9, 0), family = "sans")
  for (k in seq_along(PANELS)) {
    pid <- PANELS[k]; e <- dd[[pid]]; o <- order(e$x)
    yr <- range(c(e$f0, e$fitted)); yr <- yr + c(-0.04, 0.10) * diff(yr)
    yat <- pretty(yr, 5); yat <- yat[yat >= yr[1] & yat <= yr[2]]
    panel(c(0, 1), yr, xat = seq(0, 1, 0.25), yat = yat, xlabels = formatC(seq(0, 1, 0.25), format = "f", digits = 2),
          ylabels = formatC(yat, format = "f", digits = 1), xlab = "x", ylab = if (k == 1L) "Function value" else "")
    points(e$x, e$fitted, pch = 16, cex = 0.30, col = COL$hs)
    lines(e$x[o], e$f0[o], col = COL$truth, lwd = 1.5)
    u <- par("usr"); lab <- bquote("MSE" %*% 10^3 * ":  " * .(sprintf("%.3f", e$mse_x1000)))
    tw <- strwidth(lab, cex = 0.8); th <- strheight(lab, cex = 0.8)
    rect(u[1] + 0.02 * diff(u[1:2]), u[4] - 0.03 * diff(u[3:4]) - 1.7 * th, u[1] + 0.03 * diff(u[1:2]) + tw, u[4] - 0.01 * diff(u[3:4]),
         col = adjustcolor("white", 0.82), border = NA)
    text(u[1] + 0.025 * diff(u[1:2]), u[4] - 0.02 * diff(u[3:4]) - 0.6 * th, lab, adj = c(0, 0.5), cex = 0.8, col = "#333333")
    mtext(as.expression(caps[[pid]]), side = 1, line = 3.1, cex = 1.0, col = COL$lab)
  }
  par(fig = c(0, 1, 0, 1), oma = c(0, 0, 0, 0), mar = c(0, 0, 0, 0), new = TRUE); plot.new()
  legend("top", horiz = TRUE, bty = "n", inset = 0.005, cex = 0.85, text.col = COL$lab, col = c(COL$truth, COL$hs), lwd = c(1.5, NA), pch = c(NA, 16),
         pt.cex = c(NA, 0.9), legend = c("True function", "Horseshoe posterior mean"), x.intersp = 0.6)
}
files <- save_figure("hs_fits", 9.0, 3.9, draw31, file.path(here, "figures"))
cat("Wrote", files, sep = "\n")
