# The model behind the applications

This is the exact model that `code/` fits in the three real-data examples (Section 3.4). All three use the same model. They differ only in the data and in the choice between two dictionaries.

## 1. Model

Each data set is a set of observations $(x_i, y_i)$, $i = 1, \dots, n$, with $x_i \in [0, 1]$:

$$y_i = f(x_i) + e_i, \qquad e_i \overset{\text{iid}}{\sim} N(0, \sigma^2). \tag{M1}$$

**Fourier dictionary** (M2), with K frequencies and 2K + 1 columns (the constant, then sin/cos pairs):

$$f(x) = \beta_0 + \sum_{k=1}^{K} \bigl[\beta_{k,s} \sin(2\pi k x) + \beta_{k,c} \cos(2\pi k x)\bigr], \qquad K = \lfloor n^{0.7} \rfloor. \tag{M2}$$

**Prior** (M3): a Horseshoe with a fixed global scale, plus a Jeffreys prior on σ, as in the `horseshoe` package:

$$\beta_j \mid \lambda_j, \sigma \sim N(0, \sigma^2 \tau^2 \lambda_j^2), \qquad \lambda_j \sim C^+(0, 1), \qquad \tau = K^{-2}\ \text{(fixed)}, \qquad p(\sigma^2) \propto 1/\sigma^2, \tag{M3}$$

for $j = 1, \dots, 2K + 1$, the constant included.

**Cosine dictionary** (M4). This is used for the two chronological series (sunspots, bikes), whose start and end levels differ. It has the same number of columns, 2K + 1, and the same highest frequency as (M2):

$$f(x) = \beta_0 + \sum_{k=1}^{2K} \beta_k \cos(\pi k x), \qquad K = \lfloor n^{0.7} \rfloor. \tag{M4}$$

(M4) is the even half of the Fourier dictionary on [0, 2]. It does not force f(0) = f(1); instead, every element has zero slope at both ends. The prior is (M3), with τ = K^{-2} and j = 1, …, 2K + 1.

**Sampler.** One chain per data set:

    horseshoe(y, X, method.tau = "fixed", tau = K^-2, method.sigma = "Jeffreys", burn = 10000, nmc = 20000)

`set.seed(20261027)` is called immediately before each call.

**Summaries**, computed from the 20,000 draws β^(m):

- f̂(x) = ξ(x)ᵀ E[β | y], the posterior mean. This is the reported curve.
- The pointwise 95% band is given by the 2.5% and 97.5% quantiles of ξ(x)ᵀ β^(m).
- A frequency k counts as *active* when the marginal 95% credible interval of one of its coefficients excludes 0. For (M2) that is either β_{k,s} or β_{k,c}; for (M4) it is β_k. The count is descriptive only.

## 2. Data

Each prepared file `data/<name>.csv` has columns t (a label for plotting), x and y.

**Sunspots.** Source: SILSO, Royal Observatory of Belgium, monthly mean total sunspot number V2.0 (https://www.sidc.be/SILSO/INFO/snmtotcsv.php).
- Window: January 1900 to December 2024, so n = 1500.
- y = √(monthly mean). t is the 15th of each month, and x_i = (i − ½)/n.
- Dictionary: cosine (M4).
- Check: each monthly mean equals the mean of the valid daily values in the daily file (https://www.sidc.be/SILSO/INFO/sndtotcsv.php).

**Bike rentals.** Source: Capital Bikeshare, Washington DC, via the UCI "Bike Sharing" data set (Fanaee-T and Gama, 2014): https://archive.ics.uci.edu/static/public/275/bike%2Bsharing%2Bdataset.zip, file `day.csv`, fields `dteday` and `cnt`.
- All 731 days of 2011–2012 are used.
- y = cnt/1000, the daily rentals in thousands, and x_i = (i − ½)/n.
- Dictionary: cosine (M4).
- Check: `cnt` in `day.csv` equals the daily sum of `cnt` in `hour.csv`.

**Wave height.** Source: NOAA NDBC buoy 46001 in the Gulf of Alaska, standard meteorological data for 2010–2023 (https://www.ndbc.noaa.gov/data/historical/stdmet/46001hYYYY.txt.gz). The raw files are included in `data/raw/buoy/`.
1. Read WVHT, the significant wave height in metres. Values ≥ 99 are missing, and times are UTC.
2. Keep a UTC day if it has at least 12 valid readings. Its value is the mean of those readings, and y = log(daily mean).
3. Thin to one day a week, d = 2010-01-01 + 7j, keeping d only if that day survived step 2. This leaves n = 650.
4. The covariate is the day of year on a 365-day year: 29 February is dropped, and later dates in a leap year are shifted back by one day. Then x = (doy − ½)/365 and t = doy.
- Dictionary: Fourier (M2), since the annual cycle is periodic.

## 3. Figure

The figure has three stacked panels: (a) sunspots, (b) bikes and (c) wave height. Each panel shows the data as small grey points, the posterior mean as a navy line, and the 95% band as a light steel-blue ribbon. It is written to `output/applications_fig.png` (10 × 10 in, 300 dpi) and to `output/applications_fig.pdf`.

## 4. Outputs

For each application, the following files are written to `output/`:

- `<name>_fit.csv` has the columns t, x, y, fhat, lo and hi.
- `<name>_summary.txt` records n, K, the dictionary, the number of columns, τ, the MCMC settings, the seed, E[σ | y], the active frequencies, the run time, and the SHA-256 of the input data.

A run with a non-default `--nmc` or `--burn` writes to `output/_quick/` instead.

## 5. Raw data handling

A prep script downloads a raw file only if it is missing. It then checks every raw file against `data/raw/<name>/SHA256SUMS.txt`, which holds the hashes from the paper's run, and stops on a mismatch. `--refresh` downloads the files again and records new hashes. Use it only to accept a revised upstream file; results may then differ from the paper.
