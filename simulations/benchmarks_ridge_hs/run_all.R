script_arg <- grep("^--file=", commandArgs(trailingOnly = FALSE), value = TRUE)
script_dir <- if (length(script_arg) > 0L) {
  dirname(normalizePath(sub("^--file=", "", script_arg[1L]), mustWork = TRUE))
} else {
  normalizePath(getwd(), mustWork = TRUE)
}

rscript <- file.path(R.home("bin"), "Rscript")
if (.Platform$OS.type == "windows") {
  rscript <- paste0(rscript, ".exe")
}

forward_args <- commandArgs(trailingOnly = TRUE)
scripts <- file.path(script_dir, paste0("function_", 1:3, ".R"))

for (script in scripts) {
  message("Running ", basename(script))
  status <- system2(rscript, c(shQuote(script), forward_args))
  if (!identical(status, 0L)) {
    stop(basename(script), " failed with status ", status, call. = FALSE)
  }
}

message("All three Ridge vs Horseshoe comparisons finished.")
