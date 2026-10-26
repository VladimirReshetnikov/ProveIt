# Integration notes

Suggested descriptive slug: `signed-growth-and-centered-transport`.
Assign the next available numbered directory at integration time; the inspected
snapshot ended at package 178, but this archive does not reserve a number.

## Recommended principal entries

1. `quartic/equations/affine209_F64/equation.json`: 209 unrestricted integers,
   degree 4, 149 squared quadratics, 5,486 collected terms, exact height 2^32.
2. `quartic/equations/affine209_F128_basis/equation.json`: same dimension and
   degree, 6,654 collected terms, exact height 2^30.
3. `pooling/equations/integer130_degree12_staged.json`: 130 unrestricted
   integers, degree 12, 70 squares, 2,475 live binary operations.
4. `pooling/equations/integer116_degree16_staged.json`: 116 unrestricted
   integers, degree 16, 56 squares, 2,433 live binary operations.
5. `pooling/equations/integer107_degree32_all4.json`: 107 unrestricted
   integers, degree 32, 47 squares, 2,419 live binary operations.
6. `compact/equation.json`: ten **strictly positive** integers, degree 190,
   119 live binary operations. Its fixed tuple is unchanged from source 172.

The intermediate F128 quartic is included for exact replay, not advertised as
an additional Pareto improvement. A 30-unrestricted-integer, degree-380
conversion of the compact form is proved in the report but is not an arity
record and has not been emitted as a separate circuit artifact.

## Proof dependency structure

- The semantic signed-horizon replacement is proved in `report/signed_growth.tex`.
  It is not justified solely by an affine substitution checker.
- Both divisibility-based scalings and the residual-basis changes have explicit
  inverse maps on integer zero sets; `quartic/verify.py` checks every coefficient.
- Pooling has a full ordinary proof in `pooling/PROOF.md` and the paper, plus
  independent exact source/pool and final-circuit checkers.
- The compact transport and center proof is in `compact/PROOF.md` and
  `report/compact.tex`; the separate checker collects the norm defect and its
  exact leading homogeneous form.
- The direct logical endpoints are `KEndpoint.c222_iff_zf_refutation` and
  `ConstructibleChoice.zf_refutation_iff_zfc_refutation`. Selected actual Lean
  sources are retained for calibration provenance. A fresh whole import-closure
  build is not claimed.
- The compact logical and arithmetic calibration is retained as an ordinary
  mathematical proof at the documented native/compiler/refutation boundary.

Please preserve domain qualifiers, coefficient-height qualifiers, the distinction
between ordinary proofs and a newly compiled proof object, and the explicit
comparison snapshot. In particular, do not list degree190 as a ten-unrestricted-
integer result or the pooled height bounds as exact collected heights.

## Rejected shortcut worth preserving

Identifying the growth and beta-spacing witnesses constrains every beta modulus
to at most `1+F^2/d`; a state with two positive labels already has product weight
at least `(1+F)^2`. The retained completeness proof cannot support that fusion.
No 208-variable theorem is asserted. The obstruction and its exact scope are
recorded in the paper to prevent an invalid future composition.

## Review and release

Run `python3 -B verify_all.py --rebuild` from this directory. The checkers use
only the Python standard library. The component checks, source replay, and
mathematical audit notes are retained under `verification/` and `reviews/`.
The manifest authenticates this release's files; it is not a logical proof.
The archive contains no repository modification or publication command.

