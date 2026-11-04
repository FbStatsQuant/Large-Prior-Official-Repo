# Real-data applications: specification (the math the code implements)

Paper: "Large series priors for adaptive and optimal Bayesian nonparametric regression" (Bedoya and Li), Section 3. Three applications replace the Galveston example. Everything is in R (R 4.4.1, packages `horseshoe` 0.2.0, `ggplot2`), in the plain style of the existing scripts.

Root: `<project>/Real data/Applications/` (in this repository: `data_applications/`)
- `code/`: scripts
- `data/`: raw downloads and the prepared analysis series
- `output/`: fits, summaries, figures

## 1. Model (identical for all three applications)

Observations (x_i, y_i), i = 1..n, x_i in [0,1]. Gaussian regression

    y_i = f(x_i) + e_i,   e_i iid N(0, sigma^2).                                   (M1)

Fourier dictionary with K frequencies, 2K+1 columns (constant, then sin/cos pairs):

    f(x) = beta_0 + sum_{k=1}^K [ beta_{k,s} sin(2 pi k x) + beta_{k,c} cos(2 pi k x) ],   (M2)
    K = floor(n^0.7)     (n = number of ORIGINAL observations; b = 0.7 fixed throughout).

Prior: Horseshoe with a fixed global scale and a Jeffreys prior on sigma, exactly as in the `horseshoe` package:

    beta_j | lambda_j, sigma ~ N(0, sigma^2 tau^2 lambda_j^2),  lambda_j ~ C+(0,1),  j = 1..2K+1 (the constant included),
    tau = K^{-2} (fixed),   p(sigma^2) ∝ 1/sigma^2.                                  (M3)

Call: `horseshoe(y, X, method.tau = "fixed", tau = K^-2, method.sigma = "Jeffreys", burn = 10000, nmc = 20000)`, single chain, `set.seed(20261027)` immediately before the call.

Cosine dictionary (M4), used for the two chronological series whose start and end levels differ (sunspots, bike); it replaces the
mirror extension of version 1, which duplicated every observation. Fit (M1) and (M3) to the n ORIGINAL points with the dictionary

    f(x) = beta_0 + sum_{k=1}^{2K} beta_k cos(pi k x),   K = floor(n^0.7),                  (M4)

i.e. the even (cosine) half of the Fourier dictionary on [0,2]: the same number of columns (2K+1) and the same highest frequency
(cos(pi 2K x) = cos(2 pi K x)) as (M2), but no constraint f(0) = f(1) (instead f'(0) = f'(1) = 0 for each dictionary element).
Prior (M3) with tau = K^{-2} and j = 1..2K+1. Columns: 1, cos(pi x), cos(2 pi x), ..., cos(2K pi x).
Active "frequency" for (M4): index k in 1..2K whose cosine coefficient has a 95% credible interval excluding 0.

MCMC length (all applications): burn = 10000, nmc = 20000, single chain, set.seed(20261027) immediately before the call.

Posterior summaries, with draws beta^(m), m = 1..20000:
- f-hat(x) = xi(x)^T E[beta | y]  (posterior mean, the reported curve);
- pointwise 95% band: the 2.5% and 97.5% quantiles over m of xi(x)^T beta^(m);
- active frequency k: for (M2), the marginal 95% credible interval (package `LeftCI`/`RightCI`) of beta_{k,s} or of beta_{k,c} excludes 0; for (M4), that of beta_k excludes 0 (k = 1..2K). This is a descriptive count only.

## 2. Data (each prepared file has columns t, x, y; t = label for plotting)

### A. Sunspots (SILSO, Royal Observatory of Belgium)
- Source: monthly mean total sunspot number, version 2.0: https://www.sidc.be/SILSO/INFO/snmtotcsv.php (';'-separated; fields: year; month; decimal date; monthly mean SN; std dev; number of observations; definitive flag).
- Window: January 1900 to December 2024, so n = 1500.
- y = sqrt(monthly mean SN), a variance-stabilising transform for counts. t = date of the 15th of the month. x_i = (i - 1/2)/n. Dictionary: cosine (M4).
- Reference check: the monthly mean equals the mean of valid daily values in https://www.sidc.be/SILSO/INFO/sndtotcsv.php (daily file; missing coded -1).

### B. Bike sharing (Capital Bikeshare, Washington DC; UCI repository; Fanaee-T and Gama, 2014)
- Source: https://archive.ics.uci.edu/static/public/275/bike%2Bsharing%2Bdataset.zip, file `day.csv`, field `cnt` (total daily rentals), `dteday`.
- Window: all 731 days, 2011-01-01 to 2012-12-31. y = cnt / 1000 (daily rentals in thousands, untransformed; version 2 used log(cnt), whose few storm days were extreme outliers that pulled the Gaussian fit below the bulk of the data). x_i = (i - 1/2)/n. Dictionary: cosine (M4).
- Reference check: `cnt` in day.csv equals the sum of `cnt` over the same date in `hour.csv`.

### C. Ocean wave height (NOAA NDBC buoy 46001, Gulf of Alaska)
- Source: https://www.ndbc.noaa.gov/data/historical/stdmet/46001hYYYY.txt.gz, YYYY = 2010..2023. These are whitespace text files with 2 header lines starting '#'. Column WVHT is significant wave height in m; values >= 99 are missing. Times are UTC.
- Daily series: for each UTC calendar day from 2010-01-01 to 2023-12-31, keep the day if it has at least 12 valid WVHT records. The daily value is the mean of the valid WVHT values that day, and y = log(daily mean).
- Weekly thinning: days d = 2010-01-01 + 7 j (j = 0,1,...) up to 2023-12-31. Keep d if present in the daily series; no substitution. This reduces serial dependence.
- Covariate: day of year on a fixed 365-day year. Drop 29 February; in leap years subtract 1 from day-of-year for dates after 29 February. x = (doy - 1/2)/365, t = doy. Dictionary: Fourier (M2) (the phase is naturally periodic).
- Expected n = 650. Reference check: the independent Python implementation from scouting gives 650 weekly rows (`DataApp_Scouting/pilots/buoy_weekly.csv`, log values; its phase mapping is in `buoy_weekly_fold365.csv`).

## 3. Figure

One figure with three stacked panels (a) sunspots, (b) bike, (c) buoy, with:
- data as small grey points;
- the posterior mean as a navy line;
- the 95% band as a light steel-blue ribbon.

Axes:
- (a) x: date; y: sqrt(sunspot number).
- (b) x: date; y: daily rentals (thousands). Full range, no clipping or annotation.
- (c) x: day of year; y: log(significant wave height, m).

Panel titles are short: "(a) Monthly sunspot number, 1900-2024", "(b) Daily bike rentals, Washington DC, 2011-2012", "(c) Significant wave height, Gulf of Alaska, 2010-2023". Output: `output/applications_fig.png` (10 x 10 in, 300 dpi, white background) and `output/applications_fig.pdf`.

## 4. Outputs per application (`output/<name>_*`)
- `<name>_fit.csv`: t, x, y, fhat, lo, hi.
- `<name>_summary.txt`: n, K, dictionary (fourier/cosine), columns, tau, nmc, burn, seed, posterior mean of sigma, the active frequencies list and count, run time, sha256 of the input data file.
- Runs with non-default nmc/burn write to `output/_quick/` instead of `output/`.

## 5. Raw data handling
Prep scripts download raw files only if absent; if present, they verify them against `data/raw/<name>/SHA256SUMS.txt` (LF line endings) and stop on mismatch. Re-downloading requires an explicit `--refresh` argument.
