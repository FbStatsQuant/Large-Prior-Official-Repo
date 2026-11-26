#!/bin/bash
# SLURM array for the scaling experiment (paper Section 3.3): 400 tasks, one per (data set, target/dictionary pair), each fitting
# all 39 sample sizes on one core (about 70 s per task; under 1 GB of memory at n = 20,000).
#
# Submit from this folder:
#   mkdir -p logs
#   Rscript worker.R 1 --quick          # compiles the sampler once (see below); then delete quick_results/ if you like
#   sbatch array.slurm
#   sbatch --dependency=afterany:<array job id> process.slurm
# Rerun only missing or failed tasks with  sbatch --array=<list> array.slurm  (process.R prints the list).
#
# The sampler (../../sampler/hs_fast.cpp) is compiled on first use into ../../sampler/.cache/. Tasks that start at the same
# moment should not share that compile cache on a network file system, so compile it once before submitting the array, as
# above; every task then loads the compiled code from the cache.
#
# Edit the account, partition and module lines for your cluster.
#SBATCH --job-name=scaling
#SBATCH --array=1-400%40
#SBATCH --account=YOUR_ACCOUNT          # edit for your cluster
#SBATCH --partition=YOUR_PARTITION      # edit for your cluster
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=2G
#SBATCH --time=00:15:00
#SBATCH --output=logs/%x_%A_%a.out
#SBATCH --error=logs/%x_%A_%a.err
set -euo pipefail
# module load R                         # edit for your cluster (R with Rcpp, RcppArmadillo, digest and a C++ compiler)
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1   # one core per task
Rscript worker.R "${SLURM_ARRAY_TASK_ID}"
