#!/bin/bash
# Submit from this folder:  mkdir -p logs && sbatch F1_array_tail.slurm
# Paths are relative to the submission directory. The --account/--partition
# and module lines are for Rice's NOTS cluster; adjust them for yours.
# Submit only after F1_array.slurm has finished.
#SBATCH --job-name=F1_horseshoe_tail
#SBATCH --account=commons
#SBATCH --partition=commons
#SBATCH --array=5001-5900%1000
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --threads-per-core=1
#SBATCH --mem=8G
#SBATCH --time=03:00:00
#SBATCH --output="logs/job_%A_%a.out"
#SBATCH --error="logs/job_%A_%a.err"

set -euo pipefail
module purge
module load GCC/14.3.0
module load R/4.5.2

export OMP_NUM_THREADS=1
export OPENBLAS_NUM_THREADS=1
export MKL_NUM_THREADS=1

Rscript "${SLURM_SUBMIT_DIR}/F1_worker.R" "${SLURM_ARRAY_TASK_ID}"
