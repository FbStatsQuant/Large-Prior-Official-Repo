# Real-data applications

*Section 3.4 · Figure 4*

This folder applies the same large series prior to three noisy public series.

| Series | n | Dictionary | Columns |
|---|---|---|---|
| Monthly sunspot number, 1900–2024 (√ scale) | 1500 | cosine | 335 |
| Daily bike rentals, Washington DC, 2011–2012 (thousands) | 731 | cosine | 203 |
| Significant wave height, NOAA buoy 46001, 2010–2023 (one day per week, log scale) | 650 | Fourier | 187 |

All three use the frequency cutoff K = ⌊n^0.7⌋, a Horseshoe with τ = K⁻², and a Jeffreys prior on σ. The chain runs 10,000 burn-in iterations and then keeps 20,000 draws. The two chronological series use cosines cos(πkx), k = 1, …, 2K, which do not force the two ends to meet. Wave height is periodic in day of year, so it uses the ordinary Fourier basis. [`MODEL.md`](MODEL.md) gives the full specification.

## Running it

From this folder:

```sh
Rscript code/prep_buoy.R          # raw NOAA files are included; checked against SHA256SUMS.txt
Rscript code/prep_sunspots.R      # downloads from SILSO, then checks SHA256SUMS.txt
Rscript code/prep_bike.R          # downloads from UCI, then checks SHA256SUMS.txt
Rscript code/run_applications.R   # fits all three: output/<name>_fit.csv, <name>_summary.txt
Rscript code/make_figure.R        # output/applications_fig.{png,pdf}
```

The sunspot fit takes about half an hour, and the bike and buoy fits take 5–8 minutes each. You can also fit a subset, as in `Rscript code/run_applications.R bike buoy`. Adding `--nmc=500 --burn=100` gives a quick check, which writes to `output/_quick/`.

SILSO revises its sunspot files every month, so the raw files of a fresh download differ from those of the paper's run (files as of October 2026). The paper's prepared series, `data/sunspots.csv`, is shipped. `Rscript code/prep_sunspots.R` downloads the current files, prepares the 1900–2024 series and leaves `data/sunspots.csv` unchanged unless the result is identical to the paper's input. `Rscript code/prep_sunspots.R --refresh` writes the prepared current data instead, which may differ from the paper. For reference, the paper's prepared series has SHA-256

```
4d8d3be7fa14a1e81c7c74c425bd0c9e7ea2513eb57e5b6b344505b5f6e4884e   (LF line endings)
bdfb32d712d9d244c93f6c4341274f3ffe377e374b0d0570aab5909df7d1eccb   (CRLF line endings, as printed in reference_outputs/sunspots_summary.txt)
```

## Files

```
applications/
├── MODEL.md               the model and data definitions
├── code/
│   ├── prep_*.R           download / verify raw data, write data/<name>.csv
│   ├── fourier_hs.R       the two dictionaries and the Horseshoe fit
│   ├── run_applications.R fit, summarize, write output/
│   ├── make_figure.R      Figure 4
│   └── common.R           paths and checksum helpers
├── data/
│   ├── buoy.csv           prepared wave-height series
│   ├── sunspots.csv       prepared sunspot series, the paper's snapshot (see above)
│   └── raw/               NOAA buoy files, plus SHA256SUMS.txt for all three sources
└── reference_outputs/     summaries of the paper run, the three fitted curves, and Figure 4
```

## Reference outputs

- `<name>_summary.txt` (paper run): n, the number of columns, τ, E[σ | y], the active frequencies and the input hash.
- `<name>_fit.csv`: what Figure 4 is drawn from, one row per observation: `t`, `x`, the data `y`, the posterior mean `fhat` and the 95% band `lo`, `hi`. No posterior draws are shipped.
  - `buoy_fit.csv` is the paper run's file. A rerun of the buoy example reproduces it byte for byte.
  - `sunspots_fit.csv` and `bike_fit.csv` were not kept from the paper run. They were regenerated from the same inputs, seed and chain length with the repository's sampler in the mode that reproduces `horseshoe` 0.2.0 draw for draw ([`../sampler`](../sampler), `floor = "package"`). The regenerated fits give the paper run's E[σ | y] to all six printed decimals and exactly its active frequencies for both series; the same procedure applied to the buoy series reproduces the paper run's `buoy_fit.csv` to within 1e-13. A rerun with `run_applications.R` should agree with them to rounding error.
- `applications_fig.png`: Figure 4 as in the paper. `Rscript code/make_figure.R --from=reference_outputs` redraws it from the three fit files; the result shows the same curves, bands and points, but fonts and anti-aliasing depend on the machine, so the image file is not byte-identical.

## Data sources

- **NOAA NDBC buoy 46001**, standard meteorological data. This is US Government data in the public domain. The raw files are included.
- **SILSO** monthly and daily total sunspot number V2.0, WDC-SILSO, Royal Observatory of Belgium, Brussels, distributed under CC BY-NC 4.0. The raw files are not included; the prepared 1900–2024 series (`data/sunspots.csv`) and the observed values in `reference_outputs/sunspots_fit.csv` are shipped under the same terms. Please cite SILSO (doi:10.24414/qnza-ac80) and Clette et al. (2014).
- **UCI Bike Sharing** (Capital Bikeshare), distributed under CC BY 4.0. The raw files are not included; `reference_outputs/bike_fit.csv` contains the daily counts divided by 1,000, a transformation of the original data, shipped under the same terms. Please cite Fanaee-T and Gama (2014), doi:10.24432/C5W894.

These data stay under their providers' terms. The repository's MIT license covers only the code.
