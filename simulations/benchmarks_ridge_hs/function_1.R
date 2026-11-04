script_arg <- grep("^--file=", commandArgs(trailingOnly = FALSE), value = TRUE)
script_dir <- if (length(script_arg) > 0L) {
  dirname(normalizePath(sub("^--file=", "", script_arg[1L]), mustWork = TRUE))
} else {
  normalizePath(getwd(), mustWork = TRUE)
}

source(file.path(script_dir, "_ridge_hs_common.R"))

config <- list(
  function_id = 1L,
  display_name = "Function 1",
  file_stem = "f1",
  formula_text = "0.5 * |sin(pi * (x - 0.5))|",
  sigma = 0.15,
  seed = 1991L,
  target = function(x) {
    0.5 * abs(sin(pi * (x - 0.5)))
  }
)

options <- parse_ridge_hs_args()
run_ridge_hs_comparison(config, options, script_dir)
