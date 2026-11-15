#!/bin/bash
# Processes F1-F3 once all worker results exist. Submit from simulations/scaling/:
#   mkdir -p logs && sbatch process_all.slurm
# Paths are relative to the submission directory. The --account/--partition
# and module lines are for Rice's NOTS cluster; adjust them for yours.
# Copies of the CSVs (with SHA256SUMS.txt) go to final/F*/, or to $LP_FINAL_DIR/F*/.
#SBATCH --job-name=LP_process
#SBATCH --account=commons
#SBATCH --partition=commons
#SBATCH --array=1-3
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --threads-per-core=1
#SBATCH --mem=16G
#SBATCH --time=24:00:00
#SBATCH --output="logs/process_%A_%a.out"
#SBATCH --error="logs/process_%A_%a.err"

set -euo pipefail

module purge
module load GCC/14.3.0
module load R/4.5.2

export OMP_NUM_THREADS=1
export OPENBLAS_NUM_THREADS=1
export MKL_NUM_THREADS=1

f="F${SLURM_ARRAY_TASK_ID}"

case "$f" in
    F1) expected=5900 ;;
    F2) expected=5900 ;;
    F3) expected=3700 ;;
    *)  echo "Invalid function: $f" >&2; exit 1 ;;
esac

raw_dir="${SLURM_SUBMIT_DIR}/${f}/results"
code_file="${SLURM_SUBMIT_DIR}/${f}/${f}_process.R"
generated_dir="${SLURM_SUBMIT_DIR}/${f}/processed"
final_dir="${LP_FINAL_DIR:-${SLURM_SUBMIT_DIR}/final}/${f}"

test -d "$raw_dir"
test -s "$code_file"

count="$(find -H "$raw_dir" -maxdepth 1 -type f -name '*.rds' | wc -l)"

echo "$f: found $count of $expected expected result files."

if [ "$count" -ne "$expected" ]; then
    echo "ERROR: $f result set is incomplete; processing stopped." >&2
    exit 2
fi

mkdir -p "$generated_dir" "$final_dir"

Rscript "$code_file"

test -s "$generated_dir/${f}_fourier.csv"
test -s "$generated_dir/${f}_spline.csv"

cp -p "$generated_dir/${f}_fourier.csv" "$final_dir/"
cp -p "$generated_dir/${f}_spline.csv" "$final_dir/"

sha256sum "$final_dir"/*.csv > "$final_dir/SHA256SUMS.txt"

echo "$f processing completed."
echo "Final files: $final_dir"
