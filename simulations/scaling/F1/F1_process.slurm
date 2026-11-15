#!/bin/bash
# Submit from this folder:  mkdir -p logs && sbatch F1_process.slurm
# Paths are relative to the submission directory. The --account/--partition
# and module lines are for Rice's NOTS cluster; adjust them for yours.
# Process all completed F1 simulations into the final Fourier and spline CSVs.
#SBATCH --job-name=F1_process
#SBATCH --account=commons
#SBATCH --partition=commons
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --threads-per-core=1
#SBATCH --mem=16G
#SBATCH --time=24:00:00
#SBATCH --output="logs/process_%j.out"
#SBATCH --error="logs/process_%j.err"

set -euo pipefail

module purge
module load GCC/14.3.0
module load R/4.5.2

export OMP_NUM_THREADS=1
export OPENBLAS_NUM_THREADS=1
export MKL_NUM_THREADS=1

result_count="$(find -H "${SLURM_SUBMIT_DIR}/results" -maxdepth 1 -type f -name '*.rds' | wc -l)"

if [[ "${result_count}" -eq 0 ]]; then
  echo "No F1 result files were found." >&2
  exit 1
fi

if [[ "${result_count}" -ne 5900 ]]; then
  echo "Warning: expected 5,900 F1 result files, but found ${result_count}."
fi

echo "Processing all ${result_count} available F1 result files."
Rscript "${SLURM_SUBMIT_DIR}/F1_process.R"
