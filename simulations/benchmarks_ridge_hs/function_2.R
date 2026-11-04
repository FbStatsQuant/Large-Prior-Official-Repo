script_arg <- grep("^--file=", commandArgs(trailingOnly = FALSE), value = TRUE)
script_dir <- if (length(script_arg) > 0L) {
  dirname(normalizePath(sub("^--file=", "", script_arg[1L]), mustWork = TRUE))
} else {
  normalizePath(getwd(), mustWork = TRUE)
}

source(file.path(script_dir, "_ridge_hs_common.R"))

config <- list(
  function_id = 2L,
  display_name = "Function 2",
  file_stem = "f2",
  formula_text = "|sin(pi * (x - 0.3))|^3 + 0.7 * |sin(pi * (x - 0.7))|^3",
  sigma = 0.07,
  seed = 1991L,
  target = function(x) {
    abs(sin(pi * (x - 0.3)))^3 +
      0.7 * abs(sin(pi * (x - 0.7)))^3
  }
)

options <- parse_ridge_hs_args()
run_ridge_hs_comparison(config, options, script_dir)
