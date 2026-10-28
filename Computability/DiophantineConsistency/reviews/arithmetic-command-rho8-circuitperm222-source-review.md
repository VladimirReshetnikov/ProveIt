# Unrestricted rho8 circuit: independent source review

Reviewer: `circuit_reduction`; source author: ROOT. Date: 2026-10-26.
Verdict: no mathematical defect found in the reviewed draft. This is a
source-only challenge, not a compiler replay, cache authentication, or acceptance
of a future modified source. No Lean process was started, dependency object
constructed, or reviewed source edited during this review.

## Exact sources

Paths below are relative to the repository root. The first four main files and
the subsequently supplied checks are under
`Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.

| Source | SHA256 |
| --- | --- |
| `ArithmeticCommandRho8CircuitPerm222.lean` | `580010fadd590c1cbbf67ef14615ebbcc468a8ee2e7edf55900a1f78af5a7c30` |
| `ArithmeticCommandRho8CircuitPerm222Checks.lean` | `2a46b5f47f2a7adf46be29ffcb8e7eebd0c3153231f05b1352d7fc53f06c8c3a` |
| `ArithmeticCommandCircuitPerm222.lean` | `24427d6d6a643245630a7ea18bc94141ac923a0fffe6a7e3ae86f5309002f75d` |
| `ArithmeticCommandRulePerm222.lean` | `e381cbdfe636090c9a6e2a0c9082b10e6f33bea22f8de2ca3a7a988283de4fe1` |
| `ArithmeticCommandLeafPerm222.lean` | `511e3e22251137fdcca7c779efa06092892990d39fdadb47777849f58cf02b88` |

The generic sources are under
`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/`:

| Source | SHA256 |
| --- | --- |
| `DominatedImplication.lean` | `bd07364a829e8a1535b0ecf1ee6ed0c292d5af35e01a6db8f152dd2610e247d8` |
| `ArithmeticTemplates254.lean` | `2031511caadb7bf794d190cea99bedfa32022197f64612cb270daceee986f65f` |
| `ArithmeticCode254.lean` | `2edf178b0061838b13299f1332d65c4fc3194207cbd0e761f129a7bcc36bdff0` |

I read the complete new main, its supplied checks, the complete Circuit, Rule,
Leaf, generic DominatedImplication, and ArithmeticTemplates254 sources. For
ArithmeticCode254 I read the constructor, dominance, and related definitions
through line 165; its hash pins the complete file without claiming a new full
review of the remainder. I did not author these reviewed sources. I previously
gave source-only challenges of Leaf and Rule; that is not independent kernel
replay of those dependencies.

## Mathematical and binding checks

`Uniform` has the required quantifier order: the finite `Circuit` witness is
chosen before the model type, its arithmetic instances, and all four inputs.
`Contract` then quantifies over every initial top and saved stack. The final
theorem keeps that order. The declaration is universe-polymorphic: for each
fixed universe parameter it supplies one witness for all models in that
universe; it does not quantify over universe levels inside Lean.

The restricted MP constructor receives the major before the minor, matching
`DominatedImplication.Restricted.mp`. It deliberately builds
`mpCircuit B.circuit minor major` and invokes `mp_contract` with the minor
contract first. Expanding the circuit gives exactly `mpBlockWord`: minor,
DROP, major, then NIP/DROP/NIP/MP and the actual cleanup AX with old counter B.
There is no weakening of the arbitrary saved-stack contract.

Both `Below` growth rules are justified by `tagged_components 0`: evaluating
either implication operand is bounded by the tagged parent. The guarded leaf
therefore receives its genuine truncated-subtraction premise. The existing
finite `rho8_all` derivation uses only these restricted rows and MP; it does
not assume arbitrary unrelated inputs satisfy `Below`. Its generic theorem
is applied to the existential uniform-contract predicate, not separately to
each numeric model/input.

The intended final definitional conversion is correct on source expansion.
`ArithmeticTemplates254.rho8` unfolds through `rho8Circuit`, `Circuit.r8`, and
tag-imp evaluation to
`wim (wim (wim c u) a) (wim (wim a c) (wim b c))`.
Evaluating the generic rho8 expression gives the identical tree. The uses of
`exact` in the restricted-leaf and final endpoint therefore have the right
definitional target; actual elaboration remains the pending compiler check.

The generic module is already imported transitively, including through
Code254/TarskiFalsity/Lukasiewicz and EnumPerm/DomRho8. No new import or
Foundation build is required by this source observation.

## Checks and limits

The supplied checks retain the outer existential, reuse the graph instance,
test nested growth through both operands, and request five axiom audits.
Useful additional focused controls would be a literal evaluated-rho8 equality,
an MP expansion with distinct minor/major symbols, the same chosen witness
paired with its graph, a specialization with `u=a+1`, and the syntactic
negative control `¬Below .input3 .input0`. These are recommendations, not
claims that additional checks were implemented or executed here.

The result concerns an externally finite circuit whose output has the actual
C222 halt-or-restored-success contract. It does not establish a represented
internal compiler, proof-code recursion, a complete proof-word history,
success without halting, machine consistency, or an HA endpoint. The literal
arithmetic graph comes from the already supplied `Circuit.defined` interface;
this review does not reauthenticate that interface's compiled closure.
