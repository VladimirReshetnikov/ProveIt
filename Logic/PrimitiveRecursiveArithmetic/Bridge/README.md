# The Foundation–ConciseIPRA bridge

The [iPRA unification plan](../UNIFICATION-PLAN.md)
records the bridge baseline and specifies work on
Foundation round trips, open sequents, and arithmetic symbol comparisons.

`IPRABridge` translates closed object-theory derivations between
`DiophantineConsistency.IPRAStandardTheory.standardTheory` and
`LeanProofs.ConciseIPRA.Prf PRAAx []`. It is an opt-in Lake library.

| API | Judgment |
| --- | --- |
| `standardToConcise` | From `standardTheory ⊢ φ` to `Prf PRAAx [] (toConciseSentence φ)` |
| `conciseToStandard` | From `Prf PRAAx [] ψ` to `standardTheory ⊢ toStandardSentence ψ` |
| `conciseProvable_iff` | `Prf PRAAx [] ψ ↔ standardTheory ⊢ toStandardSentence ψ` |

The proofs go through Foundation's equality-only reference theory. The
translators preserve term substitution and quantifier-free formulas. They
transport proof rules and supply derivations for the images of the arithmetic
axioms in the destination theory. In the Foundation-to-Concise direction,
a native order atom `s < t` becomes the equation that its comparison code
returns one. `standardOrderRoundtrip` proves this substitution preserves a
Foundation sentence up to provable biconditional. The Concise-to-Foundation-to-Concise translation reproduces the
original Concise sentence exactly. The other composite can replace a
positive-arity zero symbol with a composition of the nullary zero symbol.

The arithmetic import uses additive left cancellation from
`IPRADerivations.Core.Semiring` at Foundation's existing `PRALanguage.addCore`
symbol. The [PA194 export](../../../Computability/BusyBeaver/Research/PA/verification/pa194/ipra/native-endpoint/README.md#conciseipra-export)
uses the existing Foundation proof of the equivalence for the literal
194-state machine.

Build the bridge and the arithmetic test from the repository root.

```sh
lake build IPRABridge
lake build +IPRABridge.Checks.Arithmetic
```

The [Lean entry point](Lean/IPRABridge.lean) gives the two theorem interfaces.
