#!/bin/bash
# Submit from this folder:  mkdir -p logs && sbatch F1_array.slurm
# Paths are relative to the submission directory. The --account/--partition
# and module lines are for Rice's NOTS cluster; adjust them for yours.
# One submission covers all 5,900 F1 simulations.
# Each array job runs two simulation IDs: i and i + 2,950.
#SBATCH --job-name=F1_horseshoe
#SBATCH --account=commons
#SBATCH --partition=commons
#SBATCH --array=1-2950%1000
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --threads-per-core=1
#SBATCH --mem=8G
#SBATCH --time=07:00:00
#SBATCH --output="logs/job_%A_%a.out"
#SBATCH --error="logs/job_%A_%a.err"

set -euo pipefail
module purge
module load GCC/14.3.0
module load R/4.5.2

export OMP_NUM_THREADS=1
export OPENBLAS_NUM_THREADS=1
export MKL_NUM_THREADS=1

first_id="${SLURM_ARRAY_TASK_ID}"
second_id="$((SLURM_ARRAY_TASK_ID + 2950))"

Rscript "${SLURM_SUBMIT_DIR}/F1_worker.R" "${first_id}"
Rscript "${SLURM_SUBMIT_DIR}/F1_worker.R" "${second_id}"
