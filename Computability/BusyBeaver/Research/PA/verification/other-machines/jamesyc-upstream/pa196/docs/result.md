# Formal theorem statements

The literal machine is `PA196.Literal.machine`. It starts in state 0 with an
all-zero binary tape and uses 196 working states (0 through 195). Its only
transition to the halting control is `(63, 1, 1, R, 196)`.

Let `H` denote `PA196.Arithmetic.haltingSentence` and let `N` be its
negation. The theory is ordinary first-order Peano arithmetic with full
induction.

| Lean declaration | Statement |
| --- | --- |
| `PA196.Literal.working_count`, `PA196.Literal.row_count` | The literal machine has 196 working states and 392 rows. |
| `PA196.Startup.startup_exact` | The blank run reaches the clean startup configuration after 58,154 steps. |
| `PA196.Arithmetic.Machine.Exact.PA.literal_binding` | The arithmetic rows agree with the corresponding literal transitions. |
| `PA196.machine_nonhalting` | The literal machine never halts from the blank tape. |
| `PA196.Arithmetic.nonhalting_true` | The standard natural numbers satisfy `N`. |
| `PA196.Arithmetic.pa_proves_nonhalting_consistency` | PA proves `N → Con(PA)`. |
| `PA196.Arithmetic.two_sided_independence` | PA proves neither `N` nor `H`. |

The paper states the roles of PA consistency and standard-model soundness
explicitly. The closed Lean corollaries use Foundation's standard-model
theorems in Lean's metatheory. The formal simulation uses the reachable
gap bound 48. The arithmetic proof projects an auxiliary 215-slot control
coding to the exact 196 working states and halt label 196.

The [Challenge](../Challenge.lean) presents PA and the literal machine
independently of the proof libraries. The [Solution](../PA196/Palomar/Solution.lean)
proves the matching `PalomarPA.PA196.two_sided_independence` and
`PalomarPA.PA196.machine_nonhalting` declarations. The [audit](../Audit.lean)
covers both proof presentations.
