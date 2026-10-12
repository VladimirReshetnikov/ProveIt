# Resonant order jets and convergent inverse transseries

A research contribution prepared for Vladimir Reshetnikov's ProveIt collection,
12 October 2026.

## Article

**Resonant Order Jets and Convergent Inverse Transseries for Polylogarithms and
Logarithmically Weighted Tails**

- `polylogarithm_resonance_and_inverse_transseries.pdf`: complete article.
- `polylogarithm_resonance_and_inverse_transseries.tex`: self-contained LaTeX
  source with an embedded bibliography.
- `INTEGRATION.md`: suggested repository placement, links, scope, and corrections.
- `source_provenance.json`: inspected repository revision, source paths, and
  the exact external PDF version to which the corrections apply.

The article gives conventional proofs of the following results.

1. Every order derivative of the polylogarithm at a positive integer has an
   exact, normally convergent Gamma–zeta resonance formula, expressed through
   complete Bell polynomials.
2. Logarithmically weighted integer-order endpoint deficits have convergent
   inverse logarithmic series. Their logarithmic support has a sharp bound,
   and its extreme coefficients satisfy an explicit Fuss–Catalan law.
3. For every fixed nonnegative integer logarithmic weight, one holomorphic
   inverse chart is uniform through order two when
   `epsilon * log(1/y)` stays in a compact real interval. The full logarithmic
   block, all exponential blocks, a coefficient recursion, and the first
   possible exponential correction are specified.
4. Univalence on the principal slit plane and an elementary strict cut-modulus
   bound give the global control required for inverse Taylor coefficients.
5. At every higher integer order, all coefficient orders have controlled
   logarithmic degree and explicit highest-logarithm coefficients.
6. At order two, the all-orders coefficient expansion in an exact Lambert
   variable has coefficients given by reciprocal-Gamma derivatives at
   negative integers.

The source audit finds two normalization errors and a false little-o
remainder in the inspected February 10, 2025 Krattenthaler–Rivoal note. It also
repairs its uniform contour-gap argument. The article proves the corrected
asymptotics independently and records the source hash. The third-party PDF
is referenced, not redistributed in this package.

## Mathematical scope

The proposed additions are compared explicitly with the relevant ProveIt
reports at commit `9ec0f0406afe7a5475b03ff65ed91f7e283979b8`.
The classical expansion, implicit-function theorem, Lagrange inversion, and
singularity transfer are established inputs, and related repository charts
are acknowledged. Worldwide priority has not been established. The package
contains no Lean formalization and does not represent a complete audit of
the two large research collections.

The uniform weighted theorem treats a **fixed integer weight and the bare
endpoint inverse**. The nonlinear feedback, coefficient crossover, growing
weight, and cutoff questions remain open. The article proposes twelve
concrete research directions and identifies which theorem each could extend.

## Build the PDF

A standard TeX Live installation with pdfLaTeX and `latexmk` is sufficient:

```sh
bash build.sh
```

The script writes temporary TeX outputs under `build/latex/` and copies the
finished PDF to the package root. It falls back to three pdfLaTeX passes
when `latexmk` is unavailable. Required packages are listed in the source;
there are no external bibliography tools, shell-escape steps, or downloaded
build dependencies. The delivered tables and figure allow building the
article without rerunning Python.

## Reproduce the diagnostics

Use Python 3.12 or another compatible recent Python. The recorded calculation
used Python 3.12.14. Install the pinned dependencies in an isolated environment
if necessary:

```sh
python -m pip install -r verification/requirements.txt
python verification/verify.py
python verification/coefficients.py
```

Fresh results go under `build/verification/`. To regenerate the shipped
tables, data, and figure:

```sh
python verification/verify.py --output data --figures figures
python verification/coefficients.py --output data
bash build.sh
```

`verification/README.md` explains evaluation methods and numerical limitations.

### Recorded checks

| Calculation | Coverage |
|---|---:|
| Exact Gamma–Bell resonance identities | 16 cases |
| Exact reversion with generic lower terms present | 6 families |
| Exact pure-dilogarithm Lambert correction | Through cubic order |
| Resonant jets versus independent defining sums | 24 cases |
| Critical normal form versus independent defining sums | 9 cases |
| Positive numerical inverse solutions | 214 cases |
| Exact rational inverse composition | Through degree 12 for orders 2, 3, 4 |
| Exact reciprocal-Gamma coefficient identities | First 4 coefficients |
| Inverse Taylor coefficients at two working precisions | 6 coefficients |
| Dilogarithm local-cut diagnostics at two cutoffs | 5 coefficient indices |

The 85-digit jet and critical-form comparisons have maximum discrepancies
below `1.81e-85` absolute and `1.45e-85` relative, respectively. Numerical inverse
residuals are below `4.03e-86` in the computed normal-form equations. Finite
coefficient calculations are repeated at precisions up to 376 decimal digits.

These are floating-point diagnostics, not interval enclosures. The scripts
record truncations and precision. Local-cut integrals intentionally omit the
remote contour and are not asserted to equal the entire coefficient at a
finite index. The general results follow from the article's proofs.

Short asymptotic truncations may fail at moderate scales. In particular, the
first critical correction for weight 2 and scaled order -2 is nonpositive at
`T=30` and `T=60`. Those rows are retained in the data. The plot uses `T=240`
to show the later asymptotic regime; its full 183-point grid is supplied.

## Package contents

- `data/*.json`, `data/*.csv`: complete recorded diagnostics and coefficients.
- `data/*.tex`: generated tables used by the article.
- `figures/critical_crossover_errors.pdf`: vector figure included in the article.
- `figures/critical_crossover_errors.png`: convenient raster preview.
- `verification/verify.py`: exact resonance/reversion checks and weighted
  inverse diagnostics.
- `verification/coefficients.py`: rational reversion, reciprocal-Gamma
  coefficients, precision repetition, and local-cut coefficient calculations.
- `build.sh`: local PDF build.
- `MANIFEST.sha256`: checksums of the delivered files, excluding this manifest.

No files in the upstream repository were modified and no commits or pull
requests were created. `INTEGRATION.md` describes the proposed integration.
