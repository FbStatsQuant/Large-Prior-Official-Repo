# Real-data applications

*Section 3.3 · Figure 2*

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

SILSO revises its sunspot file every month, so a fresh download usually won't match the paper's hash. `prep_sunspots.R --refresh` accepts the current file. For reference, the paper's prepared `data/sunspots.csv` has SHA-256

```
bdfb32d712d9d244c93f6c4341274f3ffe377e374b0d0570aab5909df7d1eccb
```

## Files

```
applications/
├── MODEL.md               the model and data definitions
├── code/
│   ├── prep_*.R           download / verify raw data, write data/<name>.csv
│   ├── fourier_hs.R       the two dictionaries and the Horseshoe fit
│   ├── run_applications.R fit, summarize, write output/
│   ├── make_figure.R      Figure 2
│   └── common.R           paths and checksum helpers
├── data/
│   ├── buoy.csv           prepared wave-height series
│   └── raw/               NOAA buoy files, plus SHA256SUMS.txt for all three sources
└── reference_outputs/     summaries of the paper run, the full buoy fit, and Figure 2
```

The reference summaries record n, the number of columns, τ, E[σ | y], the active frequencies and the input hash. A rerun of the buoy example reproduces `reference_outputs/buoy_fit.csv` byte for byte.

## Data sources

- **NOAA NDBC buoy 46001**, standard meteorological data. This is US Government data in the public domain. The raw files are included.
- **SILSO** monthly and daily total sunspot number V2.0, Royal Observatory of Belgium. Not redistributed here. Please cite SILSO (doi:10.24414/qnza-ac80) and Clette et al. (2014).
- **UCI Bike Sharing** (Capital Bikeshare). Not redistributed here. Please cite Fanaee-T and Gama (2014), doi:10.24432/C5W894.

These data stay under their providers' terms. The repository's MIT license covers only the code.
