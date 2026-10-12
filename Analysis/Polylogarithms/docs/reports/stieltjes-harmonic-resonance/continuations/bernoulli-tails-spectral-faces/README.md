# Bernoulli Cancellation, Harmonic Gaps, and Spectral Faces

Research continuation prepared for Vladimir Reshetnikov, 11 October 2026.

The article develops an all-power Bernoulli cancellation law for trigamma
and repeated even-order Hurwitz tails, explicit fifth- and sixth-power
identities, a complete resonant Laurent family, the completed order-ten
reconstruction theorem, several-marker Gamma–Stieltjes identities, and an
all-order spectral decomposition into ordinary simplex-face integrals.

## Read and reuse

- `Bernoulli_Tails_and_Spectral_Faces.pdf` is the complete article.
- `Bernoulli_Tails_and_Spectral_Faces.tex` is the complete standalone LaTeX
  source. It requires no other project files to compile.
- `article.tex`, `preamble.tex`, `references.tex`, and `sections/` are the
  modular sources used to generate the standalone source.
- `integration/INTEGRATION.md` maps results to the source questions and
  explains claim boundaries and proposed status changes.
- `CLAIM_STATUS.json` records proved, inherited, partially resolved, and
  still-open claims in machine-readable form.
- `PROVENANCE.json` records the pinned repository baseline, source hashes,
  and primary literature.
- `verification/` contains executable certificates, numerical diagnostics,
  successful records, build receipts, and environment versions.

## Source baseline

Repository: <https://github.com/VladimirReshetnikov/ProveIt>

Pinned commit: `da2792fc9cc8ef19c6a314be6c65e1437fbdc66b`.

The canonical manuscript and all five incoming archives dated 11 October
2026 were considered when choosing the research targets. Source material
is attributed in the article. The package does not modify the baseline
repository or claim that the Gaussian S6 and revised S8 period conjectures
are solved.

## Build the PDF

Use a local TeX distribution with `pdflatex`, Latin Modern, AMS packages,
`mathtools`, `mathrsfs`, `geometry`, `microtype`, `xcolor`, `booktabs`,
`longtable`, `enumitem`, `fancyhdr`, `hyperref`, and `bookmark`.

```bash
python build.py
```

The script flattens the modular inputs, runs three TeX passes in a temporary
directory, and writes the standalone source, PDF, and build logs. Alternatively,
compile the standalone source directly with `pdflatex` three times.

## Replay the mathematics

The exact tested Python dependency versions are in `requirements.txt`.
The delivered run used Python 3.12; see `verification/environment.json`.

```bash
python -m pip install -r requirements.txt
python verification/run_all.py --exact
python verification/run_all.py --numerical
```

The exact group is the default when neither option is given. Both flags
may be supplied together. No replay requires network access, a repository
checkout, Sage, Mathematica, or a proprietary computer algebra system.
The standard-library even-tail certificate can also be run on its own.

The exact group includes the independent finite-cutoff Bernoulli replay,
the quintic ordinary identity, rational coordinate determinants, the missing
order-ten matrix, the inherited polynomial and modular certificates, the
large-order integer comparison, and the marked-gap partition algebra.
The numerical group contains higher-precision ordinary sums and independent
Gamma/Stieltjes and spectral-integral comparisons. Some quadrature programs
take several minutes.

Successful original results are included. The runner records each exit code
and writes a separate log. A `--quick` option exists on the inherited
order-ten dependency verifier for development, but the supplied complete
replay does **not** use it. Full replay rebuilds the polynomial determinant
rather than trusting the supplied coefficient table.

Numerical residuals are diagnostics, not interval enclosures. Exact rank
statements concern the specified formal rational coordinate systems and
do not prove arithmetic independence of their evaluated constants. The
analytic convergence and continuation arguments are in the article.

## Check archive integrity

Before rebuilding or rerunning scripts that rewrite their output records:

```bash
python verification/verify_manifest.py
```

`SHA256SUMS` covers the delivered files other than itself. Rebuilding a PDF
or rerunning timed verifiers can change hashes even when every mathematical
check still passes. The checksums certify the delivered snapshot, not
bitwise reproducibility of TeX timestamps or elapsed-time fields.
