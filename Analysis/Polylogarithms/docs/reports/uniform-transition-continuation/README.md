# Uniform Transitions and Integral Structures in Polylogarithmic Analysis

A research continuation prepared for the ProveIt polylogarithms manuscript,
10 October 2026.

**Baseline commit:** `cc34f73596336f2466d9754cb0f3635bd2bedade`.
The audit includes the consolidated manuscript and all six incoming research
archives deposited at that commit. Existing incoming proofs are credited;
they are not counted again as new contributions.

## Read the article

- `article.pdf`: the complete typeset article.
- `article.tex`: assembled source, containing all text and proofs; its one
  diagnostic figure is provided in `figures/`.
- `sections/`: modular source sections for editorial integration.
- `preamble.tex`, `frontmatter.tex`, `references.tex`: editable shared sources.

The article proves:

1. An all-orders relative harmonic saddle expansion as the outer exponent
   tends to infinity, uniformly for every integer depth and every positive
   shift, with no bound on the exponent/depth ratio.
2. An all-orders inverse of the first-pole transition, with explicit first
   and second logarithmic correction polynomials.
3. A joint reflected log-gamma transition when both exponents grow near
   `n/m = log m`, including two explicit corrections and exact all-order
   coefficient identities.
4. Strict monotonicity of the reflected log-gamma slope ratio, with an exact
   computer-assisted proof. This gives a unique nondegenerate saddle and a
   uniform all-orders expansion for every compact positive proportional
   exponent range, as well as balanced-moment and rate-function corollaries.
5. An integral grid basis and finite resolution for weighted distribution
   modules over arbitrary rings, followed by the complete two-prime
   primitive-grid cokernel, Smith factors, ordinary-weight torsion, modular
   ranks, and optimal reduction denominators. The broad universal-distribution
   freeness/resolution principle is explicitly attributed to its classical
   predecessors; the concrete cokernel calculation is the main extension.
6. An exact shuffle identity proving that the two stored weight-seven S6
   candidates are equivalent. **S6 itself remains conjectural.**

The article also gives precise editorial corrections and a research agenda.
“Additional” means relative to the audited material; no exhaustive global
priority claim is made.

## Build

With Python 3 and a standard TeX Live installation:

```sh
python3 build_article.py
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

If `latexmk` is unavailable, run `pdflatex article.tex` until references settle
(normally two or three passes). To edit, change the modular sections and
reassemble. The assembled source is also directly compilable from the unpacked
bundle. To regenerate the diagnostic figure from JSON, additionally install
matplotlib and run `python3 code/plot_diagnostics.py`.

## Replay verification

The core programs require Python 3.10+, SymPy, and mpmath. Versions used for
the delivered verification are recorded in `provenance/verification_receipt.json`.

```sh
python3 verify.py
```

This replays exact symbolic checks, all integral matrix checks, the exact
interval proof, and the short Hurwitz diagnostic in an isolated temporary
copy. It leaves the delivered source data unchanged and writes a new receipt.

To additionally replay the longer defining-integral diagnostics:

```sh
python3 verify.py --numerical
```

The harmonic and joint-moment quadratures are numerical diagnostics, not
interval certificates. The reflected-slope verifier **is** an exact interval
certificate and uses only the Python standard library:

```sh
python3 code/moments/certify_gamma_saddle.py
```

Its complete middle-interval coverage is combined with the analytic endpoint
proof in the article. No floating-point special functions or assumed decimal
constants enter that proof. The exact S6-equivalence verifier is also
dependency-free:

```sh
python3 code/gaussian/verify_s6_equivalence.py
```

## Evidence and integration files

- `code/harmonic/`: exact inverse compiler and stable quadrature diagnostics.
- `code/moments/`: two independent correction derivations, all-order generator,
  exact interval proof, independent audit, and quadrature diagnostics.
- `code/distribution/`: polynomial normal forms and complete verification
  records (59 levels, 19 determinants, 112 finite-characteristic resolutions,
  and 504 Smith specializations).
- `code/gaussian/`: exact candidate equivalence and independent inverse audit.
- `editorial/INTEGRATION.md`: suggested insertion points and status changes.
- `editorial/proposed_corrections.patch`: two minimal source corrections,
  checked against the pinned source; no external repository was modified.
- `provenance/`: immutable source/archive receipts, verification and PDF QA
  records, and a bounded literature-search note.
- `MANIFEST.sha256`: checksums for delivered files, excluding itself.

The archive intentionally omits the very large inconclusive S6 search matrix.
Its scope and stopping point are reported in the article. That incomplete
search establishes neither membership nor nonmembership in a relation span.

## Mathematical cautions for integration

- Keep all compactness assumptions. The harmonic saddle theorem allows all
  shifts; the inverse theorem and proportional moment theorem use compact
  positive parameter sets. The joint moment transition keeps its transition
  parameter in a compact positive interval.
- The full integral distribution quotient is free; torsion belongs to the
  cokernel of the primitive-grid inclusion. No arithmetic independence of
  evaluated special values is claimed.
- Ordinary weights `t_p = 1` correspond to Hurwitz order zero, not order one.
  At spectral poles, combine meromorphic terms before specializing.
- The two-prime notation `h_p = ord_p(ell)` indexes a residual layer and
  differs from the complementary indexing in the general determinant formula.
- The two S6 forms should share one conjecture label. Their equivalence is
  proved; their common value is not.
