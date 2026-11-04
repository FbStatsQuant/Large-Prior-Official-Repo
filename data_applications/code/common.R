# =====================================================================
# common.R -- shared helpers for the data-application scripts
# (added for the public repository; not part of the original run).
#
#   app_root()          the data_applications/ folder: the parent of the folder
#                       holding the running script, or the LP_APP_ROOT
#                       environment variable when it is set.
#   sha256_file(f)      SHA-256 of a file's bytes (package 'digest', so no
#                       external 'sha256sum' program is needed).
#   write_sha256sums()  writes SHA256SUMS.txt in the "<hash> *<name>" format of
#                       `sha256sum -b`, which `sha256sum -c` also accepts.
#   check_sha256sums()  TRUE when every file listed in SHA256SUMS.txt exists
#                       and has the listed hash.
# =====================================================================

library(digest)

app_root <- function() {
  env <- Sys.getenv("LP_APP_ROOT", unset = "")
  if (nzchar(env)) return(normalizePath(env, winslash = "/", mustWork = TRUE))
  file_arg <- grep("^--file=", commandArgs(trailingOnly = FALSE), value = TRUE)
  if (length(file_arg) == 0L) {
    stop("Run this script with Rscript, or set LP_APP_ROOT to the data_applications folder.")
  }
  script <- normalizePath(sub("^--file=", "", file_arg[1L]), winslash = "/", mustWork = TRUE)
  dirname(dirname(script))
}

sha256_file <- function(f) digest(file = f, algo = "sha256")

write_sha256sums <- function(dir, files, sums_file = file.path(dir, "SHA256SUMS.txt")) {
  lines <- sprintf("%s *%s", vapply(file.path(dir, files), sha256_file, ""), files)
  con <- file(sums_file, "wb"); writeLines(lines, con, sep = "\n"); close(con)
  invisible(lines)
}

# Raw data handling (METHODS_SPEC.md Section 5), shared by the three prep scripts.
#   default:   download any missing raw file, then verify every raw file against
#              the shipped SHA256SUMS.txt (the hashes of the paper's run) and stop
#              on a mismatch;
#   --refresh: download everything again and record the new hashes (use this
#              only to accept a revised upstream file; results may then differ
#              from the paper).
prepare_raw <- function(raw, raw_files, download_all,
                        refresh = "--refresh" %in% commandArgs(trailingOnly = TRUE)) {
  sums <- file.path(raw, "SHA256SUMS.txt")
  if (refresh) {
    download_all()
    write_sha256sums(raw, raw_files)
    cat("--refresh: downloaded and wrote a new SHA256SUMS.txt\n")
    return(invisible(TRUE))
  }
  if (!all(file.exists(file.path(raw, raw_files)))) {
    download_all()
    cat("downloaded the raw files\n")
  }
  if (!file.exists(sums)) stop("SHA256SUMS.txt is missing; use --refresh to record new hashes")
  if (!check_sha256sums(raw)) {
    stop("raw files do not match SHA256SUMS.txt (hashes of the paper's run). ",
         "The source may have been revised; rerun with --refresh to accept the current version.")
  }
  cat("raw files verified against SHA256SUMS.txt\n")
  invisible(TRUE)
}

check_sha256sums <- function(dir, sums_file = file.path(dir, "SHA256SUMS.txt")) {
  lines <- readLines(sums_file, warn = FALSE)
  lines <- lines[nzchar(trimws(lines))]
  hash  <- sub("^([0-9a-fA-F]{64}) [ *](.*)$", "\\1", lines)
  name  <- sub("^([0-9a-fA-F]{64}) [ *](.*)$", "\\2", lines)
  ok <- vapply(seq_along(name), function(i) {
    f <- file.path(dir, name[i])
    file.exists(f) && identical(tolower(sha256_file(f)), tolower(hash[i]))
  }, logical(1))
  for (i in which(!ok)) cat("  mismatch or missing:", name[i], "\n")
  all(ok)
}
