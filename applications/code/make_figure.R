# =====================================================================
# Three-panel figure of the real-data applications (MODEL.md, Section 3).
# Plotting only: reads output/<name>_fit.csv (t, x, y, fhat, lo, hi) written
# by run_applications.R; no statistics are computed here.
#   data: small grey points; posterior mean: navy line; 95% band: light
#   steel-blue ribbon. Panels stacked with grid viewports.
# Writes output/applications_fig.png (10 x 10 in, 300 dpi, white) and .pdf.
# Usage (from any working directory):
#   Rscript make_figure.R                           # from output/ (your own run)
#   Rscript make_figure.R --from=reference_outputs  # from the shipped fits, no fitting
# --from=DIR names the folder holding the three <name>_fit.csv files, relative
# to applications/. The figure is always written to output/.
# =====================================================================

# Locate this script's folder and load the shared helpers (common.R); the
# applications/ root is found from there (or from LP_APP_ROOT).
local({
  a <- grep("^--file=", commandArgs(trailingOnly = FALSE), value = TRUE)
  d <- if (length(a)) dirname(sub("^--file=", "", a[1L])) else file.path(Sys.getenv("LP_APP_ROOT", "."), "code")
  source(file.path(d, "common.R"))
})
root <- app_root()

library(ggplot2)
library(grid)

args <- commandArgs(trailingOnly = TRUE)
unknown <- args[!grepl("^--from=", args)]
if (length(unknown)) stop("unknown argument: ", paste(unknown, collapse = " "),
                          " (the only option is --from=DIR)")
from <- sub("^--from=", "", grep("^--from=", args, value = TRUE))
if (length(from) > 1L) stop("give --from= once")
in_dir  <- file.path(root, if (length(from) == 1L) from else "output")
out_dir <- file.path(root, "output")
dir.create(out_dir, showWarnings = FALSE, recursive = TRUE)
read_fit <- function(name) {
  f <- file.path(in_dir, paste0(name, "_fit.csv"))
  if (!file.exists(f)) stop("missing ", f, ": run run_applications.R first, or use --from=reference_outputs")
  read.csv(f, colClasses = c(t = "character"))
}

## ---------------------------------------------------------------------
## 1. One panel: grey data points, steel-blue 95% band, navy posterior mean
## ---------------------------------------------------------------------
fit_panel <- function(fit, points, title, xlab, ylab) {
  ggplot(fit, aes(x = t)) +
    geom_ribbon(aes(ymin = lo, ymax = hi), fill = "lightsteelblue", alpha = 0.7) +
    geom_point(data = points, aes(y = y), colour = "grey55", size = 0.4) +
    geom_line(aes(y = fhat), colour = "navy", linewidth = 0.6) +
    labs(title = title, x = xlab, y = ylab) +
    theme_minimal(base_size = 10) +
    theme(plot.title = element_text(size = 10))
}

## ---------------------------------------------------------------------
## 2. (a) sunspots
## ---------------------------------------------------------------------
sun   <- read_fit("sunspots")
sun$t <- as.Date(sun$t)
p_a <- fit_panel(sun, sun, "(a) Monthly sunspot number, 1900-2024",
                 "date", "sqrt(sunspot number)")

## ---------------------------------------------------------------------
## 3. (b) bike, daily rentals in thousands, full range
## ---------------------------------------------------------------------
bike   <- read_fit("bike")
bike$t <- as.Date(bike$t)
p_b <- fit_panel(bike, bike, "(b) Daily bike rentals, Washington DC, 2011-2012",
                 "date", "daily rentals (thousands)")

## ---------------------------------------------------------------------
## 4. (c) buoy, against day of year
## ---------------------------------------------------------------------
buoy   <- read_fit("buoy")
buoy$t <- as.numeric(buoy$t)
p_c <- fit_panel(buoy, buoy, "(c) Significant wave height, Gulf of Alaska, 2010-2023",
                 "day of year", "log(significant wave height, m)")

## ---------------------------------------------------------------------
## 5. Stack the three panels with grid viewports; write PNG and PDF
## ---------------------------------------------------------------------
draw_figure <- function() {
  grid.newpage()
  pushViewport(viewport(layout = grid.layout(3, 1)))
  panels <- list(p_a, p_b, p_c)
  for (i in 1:3) print(panels[[i]], vp = viewport(layout.pos.row = i, layout.pos.col = 1))
}

png(file.path(out_dir, "applications_fig.png"), width = 10, height = 10, units = "in",
    res = 300, bg = "white")
draw_figure()
invisible(dev.off())

pdf(file.path(out_dir, "applications_fig.pdf"), width = 10, height = 10, bg = "white")
draw_figure()
invisible(dev.off())

cat(sprintf("fits read from %s\nfigure written to %s (applications_fig.png, .pdf)\n", in_dir, out_dir))
