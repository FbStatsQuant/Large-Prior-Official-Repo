#!/bin/bash
# Submit from this folder:  mkdir -p logs && sbatch F3_array.slurm
# Paths are relative to the submission directory. The --account/--partition
# and module lines are for Rice's NOTS cluster; adjust them for yours.
# One submission covers all 3,700 F3 simulations.
# Each array job runs two simulation IDs: i and i + 1,850.
#SBATCH --job-name=F3_horseshoe
#SBATCH --account=commons
#SBATCH --partition=commons
#SBATCH --array=1-1850%500
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --threads-per-core=1
#SBATCH --mem=8G
#SBATCH --time=09:00:00
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
second_id="$((SLURM_ARRAY_TASK_ID + 1850))"

Rscript "${SLURM_SUBMIT_DIR}/F3_worker.R" "${first_id}"
Rscript "${SLURM_SUBMIT_DIR}/F3_worker.R" "${second_id}"
