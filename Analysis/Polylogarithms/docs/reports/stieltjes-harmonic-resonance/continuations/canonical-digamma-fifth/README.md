# Canonical Digamma Polynomials and the Fifth Harmonic Bridge

**Laurent coefficients, polygamma primitives, and finite reconstruction of even-tail moments**  
Research continuation prepared for the ProveIt project, 11 October 2026.

## Read the article

- `Canonical_Digamma_and_Fifth_Moment.pdf` is the complete article.
- `Canonical_Digamma_and_Fifth_Moment.tex` is the standalone TeX source.
- `article.tex`, `sections/`, and `references.tex` are the editable modular sources.

The article proves the fifth digamma-power finite-part identity requested in
Question 1 of the incoming quartic report and the finite-prefix moment
generation requested in Question 8. It also establishes the scalar
Gamma–Appell residue normalization, the exact Gamma–polygamma ordinary
integral, all-degree inverse-Gamma differential finite parts, and normalized
primitive and derivative identities.

Question 2 receives a precise residue-normalization theorem and an exact
differential construction. Its stronger scalar arithmetic-elimination
claim remains open. The first-q prefix for unequal even orders and
arithmetic independence of the displayed constants are not asserted.
The manuscript's S6 and revised S8 ladder identities remain conjectural.

## Build

With a standard TeX Live installation including `pdflatex` and preferably
`latexmk`, run from this directory:

```bash
python3 build.py
```

The script builds the PDF, regenerates the standalone source, rejects
LaTeX layout/reference warnings, and writes `results/build_record.json`.
Intermediate TeX files go into `_build/`. To regenerate only the standalone
source, use `python3 build.py --source-only`.

Alternatively, compile `Canonical_Digamma_and_Fifth_Moment.tex` directly
with pdflatex until its references stabilize. It has no external source
inputs, figures, or bibliography databases.

## Replay the mathematics

Install the two Python dependencies from `requirements.txt`, then run:

```bash
python3 verify_all.py
python3 verify_all.py --full
```

The first command replays the exact finite identities. The second adds
the slower independent numerical evaluations. All scripts run offline.
The recorded JSON results are included so the article can be reviewed
before rerunning higher-precision quadrature.

The exact checks use finite harmonic quasi-shuffle algebra and rational
polynomial calculations. Their finite scope is documented; the general
analytic and all-degree statements are proved in the article. Numerical
residuals are floating-point diagnostics, not interval certificates.
The accompanying `results/` files distinguish these forms of evidence.

## Main verification files

| File | Purpose |
|---|---|
| `code/harmonic_algebra.py` | Finite harmonic words, quasi-shuffle algebra, low-weight reductions |
| `code/verify_fifth.py` | Fifth-power finite-sum and endpoint ledger, 87 exact checks |
| `code/numeric_fifth.py` | Independent finite-part quadrature and arithmetic sums |
| `code/verify_scalar.py` | Scalar defects, Gamma recurrences and finite-part convolutions, 94 checks |
| `code/verify_gamma.py` | Gamma residues and removable values, 202 checks, plus ordinary-integral diagnostics |
| `code/verify_tail_rank.py` | Bernoulli matrices, explicit inverse and mixed sum, 1,582 checks |
| `code/check_young_sign.py` | Numerical control of the published Stieltjes sign description |

## Provenance and integration

The reference snapshot is
`b7667ae40a2957eed9a53d8559d53a3ee20dd1c1` of
[VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt).
The two principal incoming sources are the quartic-tail report and the
Barnes report dated 11 October 2026. Exact source paths, Git blob hashes,
and selected member SHA-256 hashes are in `provenance/`.

`integration/INTEGRATION.md` proposes theorem placement and exact status
updates. `claims.json` separates proved results, inherited identities,
consequences, open questions, and the narrow published sign correction.

The normalized Gamma generator, integer harmonic Bell coefficients,
the first ordinary-integral case, and the Cauchy coefficient series have
prior literature, attributed in the article. This package makes precise
progress relative to the inspected repository; it does not claim an
exhaustive worldwide priority search.

`SHA256SUMS` covers the delivered package members. Rebuilding or rerunning
the scripts can update result metadata, so verify that manifest before
making such changes if an exact archive-integrity check is desired.
