# Four-case guarded axiom reduction

`PA194GuardedAxiomReductionFour.lean` reduces ordinary PAeq source-axiom supply to the four typed fixed axioms in `remainingFixedAfterSuccCongruence` (addition congruence, multiplication congruence, addition-successor, multiplication-successor), plus the translated closed induction axiom for every internally valid arity-one property. This last quantification includes nonstandard internal codes. `PA194GuardedInterpretationAxiomsFour.lean` applies the result to identity packets and proves the exact `Interpretation.axioms` field, under those assumptions. The guarded environment is retained throughout.

Replay from the repository root, with a fresh output directory:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-interpretation-axioms-four.sh "$PWD" /dev/shm/pa194-interpretation-axioms-four-repo-NEW-new
```

The replay compiles the two sources and an axiom-report module, requiring two reports and rejecting `sorryAx`. It retains the repository-built guarded-calculus, fixed-five, ordinary packet and other object overlays and the independently replayed fixed-four, successor congruence and order-isomorphism-successor overlays listed in the checker; Foundation and package objects are prebuilt. This is a Lean theorem about arbitrary candidate PRA models whose arithmetic reduct satisfies classical IΣ₁, not a native iPRA theorem or a full compiler.
