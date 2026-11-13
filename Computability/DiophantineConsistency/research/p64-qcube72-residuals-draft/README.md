# Five residuals of an actual 72 zero

[`FreeMainGraphResiduals.residuals`](FreeMainGraphResiduals.lean) passed its
[guarded Lean check](observations/attempt01/result.json). For any natural
ports, every positive zero of the generated 72 graph in an `IΣ₁` model gives
`A0=1`, `Na=1`, and `M=W=Lt=0` in the model difference ring. The proof splits
the nonnegative sum of squares and uses the unchanged first/transport
expressions and the checked transport-based exclusion of the negative unit.

Lean exited 0 with `[propext, Classical.choice, Quot.sound]`, no warnings or
`sorryAx`, stable direct guards and no monitor stop. Output object SHA-256:
`3c25b31eb0baa9aa8c9148d75da59af554978371b6b3a9eea5bf7dea51a73720`.
The source comment saying “unchecked draft” predates this check and is retained
for hash linkage. Direct providers inherit transitive, dynamic and
between-sample ancestry.

This establishes the residual split only. The signed half-index argument
still needs its norm translations, compact-port window and other hypotheses;
no `m=R`, reverse implication or iPRA endpoint is claimed here.
