#!/bin/bash
# SLURM job that checks and summarizes the scaling experiment after array.slurm (paper Section 3.3). Submit from this folder:
#   sbatch --dependency=afterany:<array job id> process.slurm
# process.R lists missing or failed tasks in processed/missing_tasks.txt and stops; otherwise summarize.R writes Table 2 and the
# numbers of the text to summary/, and make_figures.R writes Figure 3 to figures/.
#
# Edit the account, partition and module lines for your cluster.
#SBATCH --job-name=scaling_process
#SBATCH --account=YOUR_ACCOUNT          # edit for your cluster
#SBATCH --partition=YOUR_PARTITION      # edit for your cluster
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=4G
#SBATCH --time=00:30:00
#SBATCH --output=logs/%x_%j.out
#SBATCH --error=logs/%x_%j.err
set -euo pipefail
# module load R                         # edit for your cluster
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
Rscript process.R
Rscript summarize.R
Rscript make_figures.R
