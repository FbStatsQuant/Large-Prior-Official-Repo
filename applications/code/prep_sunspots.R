# prep_sunspots.R -- MODEL.md Section 2A, 5. Output: data/sunspots.csv (t, x, y)
# Usage: Rscript prep_sunspots.R [--refresh]
#
# data/sunspots.csv, the prepared series the paper used, ships with the
# repository, so this script is only needed to rebuild it from SILSO.
# SILSO appends a month to its files every month, so the raw files of a fresh
# download no longer have the hashes recorded for the paper's run (files as of
# October 2026). That is reported and is not an error here: the strict check is
# on the prepared series, January 1900 to December 2024, which must be
# identical to the paper's input.
#   default:   rebuild from the downloaded files; stop, and leave the shipped
#              data/sunspots.csv untouched, unless the result is identical to
#              the paper's input;
#   --refresh: download again, record the new raw hashes and write whatever the
#              current files give (the current-data workflow; results may then
#              differ from the paper).
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

# Raw data handling (MODEL.md Section 5): see prepare_raw() in common.R.
# strict = FALSE: a raw-file mismatch is reported; the prepared series is checked below.
refresh <- "--refresh" %in% commandArgs(trailingOnly = TRUE)
raw_ok  <- prepare_raw(raw, raw_files, download_all, strict = FALSE)

# SHA-256 of the paper's prepared data/sunspots.csv: with LF line endings, and
# with CRLF line endings (the paper's run wrote the file on Windows; this second
# value is the input hash printed in reference_outputs/sunspots_summary.txt).
paper_sha256 <- c("4d8d3be7fa14a1e81c7c74c425bd0c9e7ea2513eb57e5b6b344505b5f6e4884e",
                  "bdfb32d712d9d244c93f6c4341274f3ffe377e374b0d0570aab5909df7d1eccb")

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
# Strict check of the prepared series against the paper's input, then write.
tmp <- tempfile(fileext = ".csv")
write.csv(out, tmp, row.names = FALSE, quote = FALSE)
same_as_paper <- sha256_file(tmp) %in% paper_sha256
unlink(tmp)
if (same_as_paper) {
  cat("prepared series (1900-2024) is identical to the paper's input",
      if (isTRUE(raw_ok)) "\n" else "(the raw files differ only outside it)\n")
} else if (refresh) {
  cat("--refresh: the prepared series differs from the paper's input; results may differ from the paper\n")
} else {
  stop("the prepared series for 1900-2024 differs from the paper's input: SILSO has revised values inside ",
       "the window. data/sunspots.csv was left unchanged. Rerun with --refresh to use the current data.")
}
write.csv(out, file.path(root, "data", "sunspots.csv"), row.names = FALSE, quote = FALSE)
cat("n =", n, " first t =", out$t[1], " last t =", out$t[n],
    " min y =", min(out$y), " max y =", max(out$y), "\n")
