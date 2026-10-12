# Connected Spectral Jets and Mixed Gamma Primitives

Research continuation for Vladimir Reshetnikov's ProveIt project, 11 October 2026.

The complete 18-page article is **article.pdf**; **article.tex** is its self-contained,
editable LaTeX source. The article contains proofs, not only proposed identities.
Publication-level novelty has not been certified, and the proofs have not been
formalized in a proof assistant or independently peer reviewed.

## Principal results

The central construction retains an independent spectral parameter for each of
m shifted linear factors. At the critical weight x^(m-1), inclusion–exclusion
has exactly the polar term

    (-1)^m (product u_j) (product s_j) / (sum s_j).

Subtracting that term produces a holomorphic function. Its derivatives give
absolutely convergent logarithmic sums with generalized Stieltjes constants.
The article derives their all-index Gauss distribution law, simultaneous
mass-collision formula, a one-dimensional Gamma/polygamma integral, a
Gamma-normalized beta antiderivative, harmonic-number coefficient expansions,
polylogarithmic generating functions, and polynomial-weight extensions.

An especially compact specialization is the eight-spectrum cubic combination:
its value and first derivative vanish at zero, while its second derivative is
exactly -2uvw/3. The third derivative is a convergent logarithmic product sum,
and at coincident shifts that sum is a single digamma integral with kernel
3 log^2(t/(u-t)) - pi^2.

## Contents

- `article.pdf`, `article.tex`: complete research article.
- `verification/verify.py`: primary exact algebra and numerical diagnostics.
- `verification/verify_supplemental.py`: independent marked-jet, antiderivative,
  complex-parameter, and polynomial-weight checks.
- `verification/export_tables.py`: regenerates the finite exact coefficient data.
- `verification/check_manifest.py`: verifies the delivered checksum manifest.
- `results/`: recorded exact checks, numerical residuals, exact coefficient
  tables, aggregate evidence, and document-review receipt.
- `integration/connected_spectral_insert.tex`: short independently labeled
  insertion fragment, without a document preamble.
- `integration/EDITORIAL_NOTE.md`: the source-specific duplicate-text correction.
- `INTEGRATION.md`, `SOURCE_AUDIT.md`, `PROVENANCE.json`: dependencies, source
  coverage, overlap cautions, and proposed placement.
- `requirements.txt`, `Makefile`, `SHA256SUMS`: reproduction and integrity files.

## Reproduction

Use Python 3.10 or later and install the two libraries in `requirements.txt`.
The delivered checks were run with the exact versions recorded in the JSON
results. No network access or repository credentials are needed by the scripts.

```sh
python verification/verify.py
python verification/verify_supplemental.py
python verification/export_tables.py
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

To check the delivered bytes without rerunning or changing them:

```sh
python verification/check_manifest.py
```

The recorded suites pass 294 finite exact assertions and 52 numerical diagnostics.
The numerical suites work at 65 decimal digits. Their tolerances and residuals
are recorded individually. They are not certified interval enclosures, and
arbitrary precision alone does not constitute a proof. The analytical proofs
are in the article. Rerunning a suite changes its elapsed-time record; rebuilding
the PDF can change its binary metadata. The delivered manifest must not be
represented as certifying those changed artifacts.

## Scope and open status

The results are an explicitly normalized connected linear-factor theory. They
do not solve the general unequal-tail optimal first-q conjecture, the Gaussian
S6 or revised S8 identities, or the general distributional collision-restriction
problem. Classical binomial continuation, first-derivative multiplicative
anomalies, divided differences, and height-one kernel calculus are acknowledged
as background rather than claimed as new discoveries.

Selected manuscript sources were read directly. The incoming archive directory
was inventoried, but its seven binary ZIP packages were not fully inspected.
`SOURCE_AUDIT.md` records this limitation; overlap checks against those deliveries
remain part of intake. No repository file was modified.
