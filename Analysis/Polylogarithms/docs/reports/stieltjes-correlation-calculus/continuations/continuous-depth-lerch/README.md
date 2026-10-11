# Continuous-Depth Lerch Calculus

Gamma kernels, all-order harmonic identities, Stieltjes convolutions, and anchored primitives.
Research continuation prepared for Vladimir Reshetnikov's ProveIt programme, 10 October 2026.

## Main result and scope

This package answers the noninteger-depth question in Section 12, Q10, of
`ProveIt_Reciprocal_Lerch_Convolutions_2026-10-10.tex` on the natural domain
Re(depth) > 0, with Re(shift) > 0 and arbitrary complex spectral orders.
An explicit Gamma-product kernel gives an ordinary convolution semigroup.
Both depths and spectral orders add. Integer TOTAL depths retain the existing
finite Hurwitz–Lerch reductions even when the individual depths are noninteger.

The article also proves a Fourier–Mellin reflection identity, a Gamma-quotient
master for all orders of alternating harmonic combinations, an explicit cubic
harmonic identity, continuous Gamma-weighted odd-polylogarithm evaluations,
a finite algorithm for every logarithmic moment, continuous-split Stieltjes
products, polygamma depth-jet identities, and all anchored shift primitives.
A local-monodromy theorem excludes a precisely specified finite integer-depth
transform class, not every possible special-function representation.

The Ramanujan Gamma transform and normalized Meixner semigroup are classical.
No historical-priority claim is made for those inputs or every low-weight sum.
The separate Gaussian S6/S8 candidates remain unresolved. No source error was
established in the inspected proof sections; extension safeguards are explicit.
These are conventional mathematical proofs, not Lean-certified results.

## Contents

- `article.tex`: standalone article source, with embedded references and table.
- `article.pdf`: compiled article.
- `code/continuous_depth.py`: mpmath kernel, entire contour profile, real Mellin
  representations, negative-order evaluations, and harmonic-jet helpers.
- `code/verify_exact.py`: 241 finite exact assertions and 3 negative controls.
- `code/verify_numeric.py`: 88 floating-point diagnostics at 50 working digits.
- `data/`: exact coefficient tables and complete per-test JSON receipts.
- `SOURCE_AUDIT.md`, `INTEGRATION.md`, `THEOREM_INDEX.md`: provenance, claim
  distinctions, source limitations, and additive placement guidance.
- `build.py`, `requirements.txt`: reproducible build and verification entry points.

All 88 diagnostics passed a scaled-residual threshold of 1e-30. The largest
observed residual was approximately 3.54e-47. These are NOT rigorous numerical
enclosures; the infinite-parameter results depend on the proofs in the article.

## Rebuild and verify

Use Python 3.10 or later. Install the two Python dependencies in a virtual
environment, then run:

```sh
python -m pip install -r requirements.txt
python code/verify_exact.py
python code/verify_numeric.py --group all --dps 50
python build.py
```

Or run `python build.py --verify` to execute both suites and build the PDF.
A LaTeX installation with `pdflatex`, `lmodern`, `amsmath`, `mathtools`,
`mathrsfs`, `microtype`, `enumitem`, `xurl`, and `hyperref` is needed for the PDF.
The TEX file also compiles independently; its coefficient table is embedded.
No online services or API keys are needed by the delivered scripts.

Run verification on a COPY during repository intake: the scripts intentionally
regenerate the evidence files under `data/`. `build.py` also refreshes the
embedded harmonic table when its generated data file is present.

## Provenance and placement

Repository reading was pinned to:
`b7667ae40a2957eed9a53d8559d53a3ee20dd1c1`.
The preceding reciprocal-Lerch report has a different internal source pin.
See `SOURCE_AUDIT.md` for the exact distinction and inspected scope.

This is an additive continuation on the reciprocal-Lerch/Mellin–Stieltjes
spine, not a replacement manuscript. `INTEGRATION.md` gives a proposed relative
placement without asserting that the target directory already exists.
No repository or persistent Library files were changed in preparing this package.
