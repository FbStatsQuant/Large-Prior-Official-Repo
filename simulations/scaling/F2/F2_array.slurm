#!/bin/bash
# Submit from this folder:  mkdir -p logs && sbatch F2_array.slurm
# Paths are relative to the submission directory. The --account/--partition
# and module lines are for Rice's NOTS cluster; adjust them for yours.
# ============================================================
#  F2_array.slurm
#  One submission covers all 5,900 F2 simulations.
#  Each array job runs two simulation IDs: i and i + 2,950.
#
#  Simulation IDs are mapped to (n, seed) inside F2_worker.R:
#      n_seq    = seq(1000, 30000, by = 500)   -> 59 values
#      seed_seq = 1:100
#      task_id  = (i_n - 1) * 100 + i_seed     -> 1 .. 5900
#  2950 array indices x 2 IDs each = 5900 = the worker's full range.
#
#  Re-submitting is safe: F2_worker.R exits immediately when the
#  result file for its (n, seed) already exists, so this single
#  script both starts a fresh run and fills in a partial one.
#  Set F2_FORCE=1 to recompute regardless.
#
#  Resources are sized from the completed first half (tasks 1-2950),
#  where runtime and MaxRSS both scale as ~n^1.7:
#    n = 15500  ->  ~15 min, 3.5 GB
#    n = 30000  ->  ~50 min, ~10.4 GB (extrapolated)
#  Worst pair (n=15500 + n=30000) is ~1.1 h, ~2.3 h under the
#  2.1x node contention observed in that run. 8 GB is NOT enough
#  for the upper half of n_seq.
# ============================================================
#SBATCH --job-name=F2_horseshoe
#SBATCH --account=commons
#SBATCH --partition=commons
#SBATCH --array=1-2950%500
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --threads-per-core=1
#SBATCH --mem=16G
#SBATCH --time=08:00:00
#SBATCH --output="logs/job_%A_%a.out"
#SBATCH --error="logs/job_%A_%a.err"

set -euo pipefail

# NOTE: ${SLURM_SUBMIT_DIR}/logs must exist before submitting -- SLURM opens the
# log files before this script runs, so it cannot create the directory itself.

worker="${SLURM_SUBMIT_DIR}/F2_worker.R"
test -f "${worker}" || {
  echo "Missing worker: ${worker}" >&2
  exit 1
}

module purge
module load GCC/14.3.0
module load R/4.5.2

export OMP_NUM_THREADS=1
export OPENBLAS_NUM_THREADS=1
export MKL_NUM_THREADS=1

first_id="${SLURM_ARRAY_TASK_ID}"
second_id="$((SLURM_ARRAY_TASK_ID + 2950))"

Rscript "${worker}" "${first_id}"
Rscript "${worker}" "${second_id}"
