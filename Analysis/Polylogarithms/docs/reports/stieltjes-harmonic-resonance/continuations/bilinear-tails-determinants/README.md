# Bilinear Alternating Tails and Harmonic Determinants

Research continuation prepared for Vladimir Reshetnikov, 11 October 2026.

Inspected ProveIt revision:
`da2792fc9cc8ef19c6a314be6c65e1437fbdc66b`.

## Read the article

- `Bilinear_Tails_and_Harmonic_Determinants.pdf` is the complete article.
- `Bilinear_Tails_and_Harmonic_Determinants.tex` is a flattened, standalone
  source with its preamble and bibliography included.
- `article.tex`, `preamble.tex`, `sections/`, and `references.tex` are the
  equivalent modular sources, intended for selective repository integration.
- `integration/STATUS_UPDATES.md` maps the results to the source questions
  and gives precise proposed corrections.
- `provenance/` records the source boundary and literature/prior-art notes.
- `verification/` contains exact replay programs and numerical diagnostics.
- `results/` contains the recorded successful runs and explicit identity data.

## Principal outcomes

1. Two finite bilinear endpoint laws for independently ordered and shifted
   alternating Hurwitz tails, with all mixed Stieltjes derivatives and
   anchored Gamma primitives.
2. A necessary and sufficient rational adjacent-tail certificate criterion,
   with explicit independently shifted polygamma kernels.
3. The complete diagonal cutoff-contact and spectral-jet formula at every
   nonpositive integer, including its dependence on cutoff translation.
4. Equality of formal harmonic degree and generic pencil rank for real
   rational moment weights, with an exact exception test at numerical cutoffs.
5. Positive finite-difference weights of every harmonic rank at the same
   critical decay; exact spectral pole orders and Gamma-product leading
   coefficients. Its two-particle cutoff also yields a depth-two polylogarithm
   generator, an explicit Euler primitive, and an ordinary-zeta endpoint.
6. A complete proof of the smaller-order-ten centered-moment reconstruction
   family, with a finite exact computer-assisted certificate and ordinary
   convergent polygamma identities.
7. A cyclotomic status correction: the first displayed complementary-sector
   coefficient already follows from two proved manuscript reductions.

The first five items have written structural proofs. Item 6 also depends on
an exact polynomial reconstruction and congruence replay, whose full input
is included. The article explicitly separates new developments, classical
ingredients, inherited project theorems, numerical diagnostics, and open
questions. It makes no arithmetic-independence or exhaustive priority claim.

## Build

The PDF was built with pdfLaTeX through `latexmk`. The TeX dependencies are
standard packages (AMS mathematics, Latin Modern, geometry, microtype,
booktabs, longtable, enumitem, hyperref, bookmark, and fancyhdr).

From the package root:

```bash
python build.py --pdf
```

This refreshes the flattened TeX and builds the PDF. `python build.py`
refreshes only the flattened TeX. Alternatively, run `pdflatex` on the
standalone TeX until cross-references settle. Build intermediates belong in
`build/` and are not needed for integration.

## Reproduce the mathematical checks

The scripts require Python 3, SymPy, and mpmath. The observed versions are
Python 3.12, SymPy 1.14.0, and mpmath 1.3.0; exact package pins are in
`requirements.txt`. The programs need no network access.

The following commands are relative to the package root:

```bash
python verification/verify_bilinear_tails.py results/bilinear_verification.json
python verification/verify_cutoff_jets.py results/cutoff_jets_checks.json
python verification/determinants/verify_exact.py
python verification/determinants/verify_numeric.py
python verification/determinants/verify_polylog.py
python verification/order10/verify_order10_completion.py --full --output results/order10_completion_checks.json
python verification/order10/eventual_threshold.py 5 --output results/order10_eventual_threshold_replay.json
python verification/order10/build_order10_identity.py
```

The determinant scripts write their new JSON next to the script. The
explicit-identity script does likewise. The archived runs of those programs
are collected under `results/` for convenient review.

The `--full` order-ten run independently reconstructs the inherited
multivariate numerator from its finite Newton/factorial matrix before
checking the new congruence; it took about one minute in the inspected
environment. Omitting `--full` skips only that reconstruction, not the new
coefficientwise congruence, exact finite matrices, threshold comparisons,
or independent Bernoulli-residue checks. The grouped certificate preserves
all 10,403 expanded polynomial coefficients in 439 groups. The threshold
program derives its norm constant from the finite entry formulas.

Numerical checks include complex shifts and orders, independent Laplace or
Mellin integrals, finite-difference endpoints, and Laurent extrapolations.
Reported residuals are diagnostics, not rigorous interval bounds. They are
not used to prove identities, nonvanishing, or independence of constants.

## Integration scope

The main branch was inspected read-only. This package is a proposed research
contribution, not a repository merge. The source and question map should
travel with any imported theorem. In particular:

- The Gamma-weighted identities concern alternating tails. The earlier
  independent ordinary-Hurwitz problem with an arbitrary outer order remains
  open.
- The order-ten theorem is uniform for every even larger order. The
  unrestricted smaller orders at least twelve and the full gap-six family
  remain open.
- Harmonic degree and moment rank are formal coordinate statements.
- The real restriction in degree sharpness and the positive-real shift
  restriction for exact pole orders are substantive.
- Finite parts retain their displayed spectral or cutoff prescription.
- The cyclotomic coefficient is an inherited consequence, not a new
  arithmetic reduction or a proof of the Gaussian S6/S8 conjectures.

No predecessor PDFs, extracted input archives, build caches, or temporary
exploration scripts are included. The necessary inherited coefficient
certificate and threshold construction are explicitly attributed in the
article and provenance notes.
