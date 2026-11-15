# prep_sunspots.R -- MODEL.md Section 2A, 5. Output: data/sunspots.csv (t, x, y)
# Usage: Rscript prep_sunspots.R [--refresh]
# Locate this script's folder and load the shared helpers (common.R); the
# applications/ root is found from there (or from LP_APP_ROOT).
local({
  a <- grep("^--file=", commandArgs(trailingOnly = FALSE), value = TRUE)
  d <- if (length(a)) dirname(sub("^--file=", "", a[1L])) else file.path(Sys.getenv("LP_APP_ROOT", "."), "code")
  source(file.path(d, "common.R"))
})
root <- app_root()
raw  <- file.path(root, "data", "raw", "sunspots")
dir.create(raw, recursive = TRUE, showWarnings = FALSE)
f_m <- file.path(raw, "SN_m_tot_V2.0.csv")   # monthly file
f_d <- file.path(raw, "SN_d_tot_V2.0.csv")   # daily file (reference check only)
raw_files <- c("SN_m_tot_V2.0.csv", "SN_d_tot_V2.0.csv")
download_all <- function() {
  download.file("https://www.sidc.be/SILSO/INFO/snmtotcsv.php", f_m, mode = "wb", quiet = TRUE)
  download.file("https://www.sidc.be/SILSO/INFO/sndtotcsv.php", f_d, mode = "wb", quiet = TRUE)
}

# Raw data handling (MODEL.md Section 5): see prepare_raw() in common.R
prepare_raw(raw, raw_files, download_all)

# Monthly file: year; month; decimal date; mean SN; std dev; n obs; definitive flag
m <- read.table(f_m, sep = ";", strip.white = TRUE, header = FALSE)
names(m)[1:4] <- c("year", "month", "decdate", "sn")

# Window: Jan 1900 - Dec 2024, n = 1500
m <- m[m$year >= 1900 & m$year <= 2024, ]
m <- m[order(m$year, m$month), ]
n <- nrow(m)
stopifnot(n == 1500, all(m$sn >= 0))

# y = sqrt(monthly mean SN); t = 15th of the month; x_i = (i - 1/2)/n
out <- data.frame(t = sprintf("%04d-%02d-15", m$year, m$month),
                  x = ((1:n) - 0.5) / n,
                  y = sqrt(m$sn))

# Reference check (assertion): |monthly - mean of valid daily| <= 0.1 for every month with valid daily values (missing = -1)
d <- read.table(f_d, sep = ";", strip.white = TRUE, header = FALSE)
names(d)[1:5] <- c("year", "month", "day", "decdate", "sn")
d <- d[d$sn >= 0, ]
dm <- tapply(d$sn, sprintf("%04d-%02d", d$year, d$month), mean)
key <- sprintf("%04d-%02d", m$year, m$month)
has <- key %in% names(dm)
diffs <- abs(m$sn[has] - as.numeric(dm[key[has]]))
cat("months with daily values:", sum(has), " max |monthly - daily mean| =", max(diffs), "\n")
if (any(diffs > 0.1)) stop("sunspots reference check failed")
# Write output only after all checks have passed
write.csv(out, file.path(root, "data", "sunspots.csv"), row.names = FALSE, quote = FALSE)
cat("n =", n, " first t =", out$t[1], " last t =", out$t[n],
    " min y =", min(out$y), " max y =", max(out$y), "\n")
