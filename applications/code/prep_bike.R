# prep_bike.R -- MODEL.md Section 2B, 5. Output: data/bike.csv (t, x, y)
# Usage: Rscript prep_bike.R [--refresh]
# Locate this script's folder and load the shared helpers (common.R); the
# applications/ root is found from there (or from LP_APP_ROOT).
local({
  a <- grep("^--file=", commandArgs(trailingOnly = FALSE), value = TRUE)
  d <- if (length(a)) dirname(sub("^--file=", "", a[1L])) else file.path(Sys.getenv("LP_APP_ROOT", "."), "code")
  source(file.path(d, "common.R"))
})
root <- app_root()
raw  <- file.path(root, "data", "raw", "bike")
dir.create(raw, recursive = TRUE, showWarnings = FALSE)
zipf <- file.path(raw, "bike_sharing_dataset.zip")
raw_files <- c("bike_sharing_dataset.zip", "day.csv", "hour.csv")
download_all <- function() {
  download.file("https://archive.ics.uci.edu/static/public/275/bike%2Bsharing%2Bdataset.zip",
                zipf, mode = "wb", quiet = TRUE)
  unzip(zipf, files = c("day.csv", "hour.csv"), exdir = raw)
}

# Raw data handling (MODEL.md Section 5): see prepare_raw() in common.R
prepare_raw(raw, raw_files, download_all)

day <- read.csv(file.path(raw, "day.csv"))
hr  <- read.csv(file.path(raw, "hour.csv"))
day <- day[order(as.Date(day$dteday)), ]
n <- nrow(day)
stopifnot(n == 731, day$dteday[1] == "2011-01-01", day$dteday[n] == "2012-12-31", all(day$cnt > 0))

# y = cnt/1000 (daily rentals in thousands, untransformed); x_i = (i - 1/2)/n
out <- data.frame(t = day$dteday, x = ((1:n) - 0.5) / n, y = day$cnt / 1000)

# Assertion: max |y*1000 - day.cnt| == 0
# round(): y*1000 in floating point is off by ~1e-12, so compare the nearest integer
err <- max(abs(round(out$y * 1000) - day$cnt))
cat("max |y*1000 - day.cnt| (after rounding to integer) =", err, "\n")
if (err != 0) stop("bike y*1000 != day.cnt")

# Reference check (assertion): day cnt == sum of hourly cnt on the same date, for every date
hs <- tapply(hr$cnt, hr$dteday, sum)
dd <- abs(day$cnt - as.numeric(hs[day$dteday]))
cat("max |day.cnt - sum(hour.cnt)| =", max(dd), "\n")
if (anyNA(dd) || any(dd != 0)) stop("bike reference check failed")
# Write output only after all checks have passed
write.csv(out, file.path(root, "data", "bike.csv"), row.names = FALSE, quote = FALSE)
cat("n =", n, " first t =", out$t[1], " last t =", out$t[n],
    " min y =", min(out$y), " max y =", max(out$y),
    " date of min =", out$t[which.min(out$y)], "\n")
