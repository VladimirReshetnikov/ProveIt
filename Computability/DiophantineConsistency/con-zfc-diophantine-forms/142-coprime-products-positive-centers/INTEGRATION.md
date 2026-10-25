# Integration notes for ProveIt

This is a proposed research intake package. No upstream repository was
modified, and no package number is assumed.

## Suggested entry

Title: **Coprime product certificates and positive Pell centers**

Date: 25 October 2026

Baseline: `e0c98c629bf10d30b695884f6b1d2ab361bdf513`, including all six
archives then present in `docs/incoming`.

New preferred points:

- Positive compact: `(variables, operations, degree)` = `(14,70,189)`,
  `(14,71,157)`, `(13,72,433)`, `(10,76,626)`, `(10,77,464)`, `(10,80,382)`.
- Direct natural quartic: `(221 variables,172 residuals,9536 terms,height
  83954186)`; sparse companion `(222,173,6821,83954028)`.

## Review order

1. Read Sections 2–5 of `report/report.pdf` for the product lemma, the exact
   P66 interface, staged sign recovery, and the two-anchor construction.
2. Check `compact_xy/PROOF.md` and `PARTIAL_Q2_PROOF.md`, especially the
   negative-transport cases, recovery of the bounded first index, the
   whole-product projection, and the delayed `q|s` conclusion.
3. Read `natural/PROOF.md` for both directions of the positive-center
   replacement, the extra aggregate digit budgets, and the noncircular
   factorial-digit bound deletion.
4. Run `python3 -B verify.py --rebuild`, inspect its receipt, and compare
   component provenance against the pinned source.

Keep the full component directories together. In particular, do not detach
a compact graph from its four fixed coefficient payloads or substitute
constants from a later native compiler. Do not detach a contracted quartic
from its complete raw graph and monic-restoration certificate.

## Proof status to preserve in a repository entry

These are ordinary arithmetic proofs, formalizable in ZFC, with exact
reconstruction and artifact checks. They compose named inherited native
or direct proof-calculus calibrations. They are not newly produced
Lean/Rocq proof terms or encoded formal ZFC derivations. The finite tests
do not determine consistency. No global simplicity or literature-priority
claim should be inferred from the bounded repository comparisons.

The compact-constant appendix and the printed natural residuals are
complete definitions, not descriptive placeholders. The final preferred
product degrees are **189, 157, and 433**. The provisional product degrees
233, 465, and 435 are not current endpoints.
