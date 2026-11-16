# Constructive trigonometric identities in iPRA

This archive accompanies **A Constructive Atlas of Trigonometric Identities in
Intuitionistic Primitive Recursive Arithmetic** (15 November 2026).

## Main result

The report gives a human-readable constructive proof architecture for most
finite families in Wikipedia's *List of trigonometric identities*, plus
principal inverse-function identities, differentiation of sine and cosine, and
the dyadic infinite cosine product. The formal interpretation uses fixed
primitive-recursive rapidly convergent dyadic names inside first-order iPRA.
Polynomial identities are unconditional. Quotient, square-root, phase, and
inverse-function identities carry explicit apartness or branch certificates.

The exact checker verifies **227 identities in 27 families**, with exact
Gaussian-rational Laurent polynomial arithmetic and **0 failures**.

## Files

- `trigonometric_identities_ipra.pdf` - compiled 23-page report.
- `trigonometric_identities_ipra.tex` - LaTeX source.
- `scripts/verify_identities.py` - exact certificate generator/checker.
- `scripts/verify_all.sh` - reproducibility wrapper.
- `artifacts/identity_certificates.json` - per-identity certificate ledger.
- `artifacts/verification_report.txt` - generated verification summary.
- `artifacts/coverage.csv` - coverage and constructive side-condition matrix.
- `Lean/TrigAlgebra.lean` - abstract algebraic Lean prototype.
- `Lean/LaurentCertificate.lean` - exact-certificate Lean data model and
  soundness outline.
- `Lean/IPRABridge.lean` - implementation blueprint on top of ProveIt's
  `ConciseIPRA.PR` and `ConciseIPRA.EqArith`.
- `SOURCES.md` - external-source and repository snapshot notes.
- `SHA256SUMS` - checksums for the packaged files.

## Reproduce the exact certificates

```bash
./scripts/verify_all.sh
```

The checker requires Python 3.11 or newer and only uses the standard library.
It performs no floating-point trigonometry and no numerical sampling.

## Rebuild the PDF

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  trigonometric_identities_ipra.tex
```

A TeX distribution containing the standard AMS, `hyperref`, `listings`, and
`fancyvrb` packages is sufficient.

## Lean status

The artifact-building environment did not contain a Lean toolchain. The Lean
files were therefore not compiled here. `TrigAlgebra.lean` is intended as a
near-term compiling Mathlib prototype. `LaurentCertificate.lean` and
`IPRABridge.lean` intentionally contain `axiom` declarations that mark the
remaining implementation obligations; the report gives a dependency-ordered
path for removing them. No claim of completed Lean verification is made.
