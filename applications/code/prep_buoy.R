# prep_buoy.R -- MODEL.md Section 2C, 5. Output: data/buoy.csv (t = day of year, x, y)
# Usage: Rscript prep_buoy.R [--refresh]
# Locate this script's folder and load the shared helpers (common.R); the
# applications/ root is found from there (or from LP_APP_ROOT).
local({
  a <- grep("^--file=", commandArgs(trailingOnly = FALSE), value = TRUE)
  d <- if (length(a)) dirname(sub("^--file=", "", a[1L])) else file.path(Sys.getenv("LP_APP_ROOT", "."), "code")
  source(file.path(d, "common.R"))
})
root <- app_root()
raw  <- file.path(root, "data", "raw", "buoy")
dir.create(raw, recursive = TRUE, showWarnings = FALSE)
raw_files <- sprintf("46001h%d.txt.gz", 2010:2023)
files <- raw_files
download_all <- function()
  for (f in raw_files)
    download.file(paste0("https://www.ndbc.noaa.gov/data/historical/stdmet/", f),
                  file.path(raw, f), mode = "wb", quiet = TRUE)

# Raw data handling (MODEL.md Section 5): see prepare_raw() in common.R
prepare_raw(raw, raw_files, download_all)

# Read all years: 2 header lines starting '#'; WVHT >= 99 is missing; times UTC
rd <- function(f) {
  z <- read.table(file.path(raw, f), skip = 2, header = FALSE, stringsAsFactors = FALSE, fill = TRUE)
  hdr <- scan(file.path(raw, f), what = "", nlines = 1, quiet = TRUE)
  hdr[1] <- sub("^#", "", hdr[1])
  names(z)[seq_along(hdr)] <- hdr
  yr <- z[[1]]; yr <- ifelse(yr < 100, yr + 2000, yr)
  data.frame(date = sprintf("%04d-%02d-%02d", yr, z$MM, z$DD), wvht = z$WVHT)
}
a <- do.call(rbind, lapply(files, rd))
a <- a[a$wvht < 99, ]

# Daily series: keep days with >= 12 valid records; daily value = mean of valid WVHT
cnt <- tapply(a$wvht, a$date, length)
mn  <- tapply(a$wvht, a$date, mean)
daily <- data.frame(date = names(cnt), nvalid = as.integer(cnt), mean = as.numeric(mn), stringsAsFactors = FALSE)
daily <- daily[daily$nvalid >= 12, ]

# Weekly thinning: d = 2010-01-01 + 7j through 2023-12-31; keep if present, no substitution
d0 <- as.Date("2010-01-01")
sched <- seq(d0, as.Date("2023-12-31"), by = 7)
sched_chr <- format(sched)
keep <- sched_chr %in% daily$date
cat("schedule days =", length(sched), " kept =", sum(keep), " dropped (no daily value) =", sum(!keep), "\n")
w <- data.frame(date = sched[keep], mean = daily$mean[match(sched_chr[keep], daily$date)])

# Day of year on a fixed 365-day year: drop 29 Feb; after 29 Feb in leap years subtract 1
doy <- as.integer(format(w$date, "%j"))
yr  <- as.integer(format(w$date, "%Y"))
leap <- (yr %% 4 == 0 & yr %% 100 != 0) | yr %% 400 == 0
is29 <- format(w$date, "%m-%d") == "02-29"
cat("29 Feb rows dropped =", sum(is29), "\n")
doy <- ifelse(leap & doy > 60, doy - 1L, doy)
w <- w[!is29, ]; doy <- doy[!is29]

# x = (doy - 1/2)/365; y = log(daily mean); t = doy
out <- data.frame(t = doy, x = (doy - 0.5) / 365, y = log(w$mean))

# Assertion: n == 650 and no NA
if (nrow(out) != 650 || anyNA(out)) stop("buoy check failed: n != 650 or NA present")
# Write output only after all checks have passed
write.csv(out, file.path(root, "data", "buoy.csv"), row.names = FALSE, quote = FALSE)
cat("n =", nrow(out), " first raw date =", format(w$date[1]), " last raw date =", format(w$date[nrow(w)]),
    " min y =", min(out$y), " max y =", max(out$y), " distinct x =", length(unique(out$x)), "\n")
