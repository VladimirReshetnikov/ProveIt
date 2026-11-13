# Formal theorem statements

The literal machine is `M6.Literal.machine`. Its initial configuration is
`M6.Startup.blank`, state 0 on a blank binary tape. Ordinary Peano arithmetic
is Foundation's first-order theory `Peano`, with full induction.
Let `H` denote `ExactHaltingFormula.traceSentence` and `N` its negation.

| Lean declaration | Statement |
| --- | --- |
| `M6.Arithmetic.PA.FinalEndpoint.literal_final_endpoint` | Under PA consistency, the exact machine has 209 working states and 418 rows, runs forever, and its exact arithmetic nonhalting sentence is true and unprovable in PA. |
| `M6.PA.literal_nonhalting` | Under PA consistency, the literal machine never halts from the blank tape. |
| `M6.Arithmetic.PA.FinalEndpoint.nonhalting_true` | Under PA consistency, the natural numbers satisfy `N`. |
| `M6.Arithmetic.PA.FinalEndpoint.pa_proves_nonhalting_consistency` | PA proves `N → Con(PA)`. |
| `M6.Arithmetic.PA.FinalEndpoint.nonhalting_unprovable` | Under PA consistency, PA cannot prove `N`. |
| `M6.Arithmetic.PA.ExactHaltingFormula.literal_binding` | Each active arithmetic row agrees with the corresponding physical transition after state relabeling. |
| `M6.Arithmetic.PA.Independence.nonhalting_irrefutable` | Under PA consistency, standard-model soundness excludes a PA proof of `¬N`. |
| `M6.Arithmetic.PA.Independence.halting_unprovable` | PA cannot prove the positive halting sentence `H`. |
| `M6.Arithmetic.PA.Independence.two_sided_independence` | PA can prove neither `N` nor `¬N`. |
| `M6.Arithmetic.PA.Independence.machine_nonhalting` | The literal machine never halts from the blank tape. |

The unconditional corollaries use Foundation's standard-model consistency
and soundness theorems in Lean's metatheory.

[Challenge](../Challenge.lean) states both headline results with explicit
syntax and provability for ordinary PA. [Solution](../Solution.lean)
identifies that proof predicate and those sentences with Foundation's
presentation and transfers literal machine runs. [Audit](../Audit.lean)
covers the proof endpoints and both compared declarations.
