# Final SW/BV and Lean consistency review

## Scope of review

Read `lean/Targets.lean`, `lean/ObjectBridge.lean`, the SW/BV section,
the scope and Lean roadmap sections, and the main document's status text.
This is a source-level mathematical and syntax plausibility review. Lean is
not installed in the environment; no compilation or kernel verification
was performed or inferred from this review.

## Result

The rational definitions match the paper's SW/BV targets. No mathematical
or obvious Lean syntax defect was found in those definitions. The file
contains executable definitions and `Prop` declarations, not proofs of
the target propositions. The object bridge contains only a conditional
transport statement and explicitly leaves its arithmetic premise open.

The sharp Brun–Titchmarsh target was already present with the correct
coefficient 2 and all-range condition `q < X`. Its comment has now been
updated to distinguish the newly supplied human proof from the still
unproved Lean target. A documentation-only module list was added. The
two uses of `Nat.dist` were replaced by an explicit definition
`natDistance a b = (a-b)+(b-a)` to make that arithmetic dependency local.
No theorem assertion or proof placeholder was added.

## Definitions checked against the mathematics

- `phi 1 = 1`; the canonical residue for modulus 1 is zero.
- The sums include index zero, but the prime, prime-power, harmonic,
  squarefree, and positive-modulus guards give the required zero term.
- `primePowerBase` searches positive exponents through n; this contains
  every exponent of a prime power equal to n. Its default zero does not
  enter a logarithm of zero because `lambdaApprox` explicitly returns zero.
- `logLower n s` uses exactly `n*(n+s+3)` terms. `logPartial` has positive
  odd denominators, and the theorem domains keep its argument at least 1.
- `errorApprox` ranges over integer endpoints and reduced canonical
  residues. The initial zero in the maximum is harmless because every
  retained absolute error is nonnegative.
- The SW target uses `floorLogTwo X`, the integer-square-root exponent,
  and positive witnesses K,C,T before every endpoint and precision.
- The BV range is `2^(t/2)/t^B` in natural arithmetic. Its rational error
  term is `Q * 2^t / 2^s`, avoiding truncated natural subtraction in an
  exponent. C and T are positive, and T<=t keeps the denominator t^A
  positive. The aggregate Q factor is retained.
- The sharp BT target uses the lower logarithm with
  `M=2^r*ceil(X/q)`. Under `1<=q<X`, M is positive, the logarithm error
  is at most `2^-r`, and the target is the exact cross-multiplied sharp
  inequality at every precision. It does not assume the asymptotic
  threshold needed by the separate `(2+1/k)` target.
- The Chebotarev count interfaces retain a positive group order and an
  eventual positive denominator. Their cross-multiplied absolute
  difference is exactly the requested `1/k` density allowance. The
  functions are explicitly fixed metalevel PR specifications, not
  object-language quantification over arbitrary functions.
- The Dirichlet constants and factorial-scaled sum agree with the paper.
  The bounded selector has a total default and retains its first successful
  prime. No evaluation of the enormous theoretical bound is requested.
- The higher-order sum/max helpers are metalevel templates. Their fixed
  instantiations must receive PR codes individually; the source does not
  provide a universal evaluator for arbitrary functions.

## Presentation synchronization noted during the review

At the time of inspection, the parent was integrating the new sharp BT
section. Consequently `paper/main.tex`, the BT row in `01_scope.tex`, and
the BT module row in `08_lean.tex` still had the earlier wording that the
exact coefficient 2 was missing. Those are known integration edits, not
mathematical defects in the targets. They must be updated before delivery.
Likewise the object-bridge documentation should list the sharp BT matrix,
with its precision parameter, as a distinct final arithmetic endpoint.

The phrase “All variables here are integers” after the SW arithmetic target
is best replaced by “All quantified variables in the arithmetic targets
range over natural numbers.” The global conventions already give this
meaning, and the Lean file implements it explicitly.

## Status boundary

Sharp BT's new human proof does not alter the missing uniform witnesses
for full Siegel–Walfisz or Bombieri–Vinogradov. The package's claims about
those theorems should remain partial. The finite computations,
absence of proof holes, and conditional bridge are not evidence that the
embedded iPRA derivations have been constructed. No assertion of iPRA
nonprovability is justified by the effectiveness discussion.

