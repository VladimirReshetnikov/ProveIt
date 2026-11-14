# Formula substitution constructor inversion

`PA194SubstInverse.lean` proves two syntactic inversion results in every
candidate-PRA model whose arithmetic reduct satisfies IΣ₁, including for
nonstandard codes. Given a well-formed formula and substitution vector, if
its substitution result is a universal formula, `subst_all_inverse` produces
its original universal body and the exact lifted-vector substitution equation.
If the result is a disjunction, `subst_or_inverse` produces both original
disjuncts and their exact substituted codes. The statements are generic over
the encoded language, so they apply to PA194's relational source language.

These results port the body of the upstream PA196
`FoundationPAeqCodeSubstitutionInverse.lean` (SHA-256
`83f299dab802d6ba0ce3e3a1742be8ff8a7e74dd17a1de6b6b3df61746968996`)
from FFL to the current LO Foundation interfaces. Upstream uses them in
`FoundationPAeqCodeInductionMatrix.additive_matrix_witness`, itself stated
under IΣ₁, to recover a quantified matrix from a substituted induction body.
This port does not establish the matrix theorem, a PA induction-axiom proof
supplier, a numerical proof compiler, or a machine reduction.

Run from the repository root with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-source-subst-inverse/check.sh
```

The final module passed a fresh suffix check using retained prerequisites;
the printed axioms contain no `sorryAx`. The full nested replay is pending.
