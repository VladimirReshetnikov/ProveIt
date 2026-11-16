# The Foundation–ConciseIPRA bridge

The [iPRA unification plan](../UNIFICATION-PLAN.md)
records the bridge baseline and specifies work on
Foundation round trips, open sequents, and arithmetic symbol comparisons.

`IPRABridge` translates object-theory derivations between
`DiophantineConsistency.IPRAStandardTheory.standardTheory` and
`LeanProofs.ConciseIPRA.Prf PRAAx []`. It is an opt-in Lake library.

| API | Judgment |
| --- | --- |
| `standardToConcise` | From `standardTheory ⊢ φ` to `Prf PRAAx [] (toConciseSentence φ)` |
| `conciseToStandard` | From `Prf PRAAx [] ψ` to `standardTheory ⊢ toStandardSentence ψ` |
| `conciseProvable_iff` | `Prf PRAAx [] ψ ↔ standardTheory ⊢ toStandardSentence ψ` |
| `standardProvable_iff` | `(standardTheory ⊢ φ) ↔ Prf PRAAx [] (toConciseSentence φ)` |
| `standardToConciseSequent` | Translate a Foundation derivation under an arbitrary assignment of Concise terms to free labels |
| `conciseToStandardSequent` | Translate a Concise derivation under an arbitrary assignment of Foundation terms to its finite scope |
| `scopedStandardSequent_iff` | Reflect a finite Foundation sequent opened at distinct variable labels |
| `scopedStandardSequent_iff_closure` | Relate a scoped derivation to the universally closed implication from its hypotheses |

The proofs go through Foundation's equality-only reference theory. The
translators preserve term substitution and quantifier-free formulas. They
transport proof rules and supply derivations for the images of the arithmetic
axioms in the destination theory. In the Foundation-to-Concise direction,
a native order atom `s < t` becomes the equation that its comparison code
returns one. `standardOrderRoundtrip` proves this substitution preserves a
Foundation sentence up to provable biconditional. The Concise-to-Foundation-to-Concise translation reproduces the
original Concise sentence exactly. The other composite can replace a
positive-arity zero symbol with a composition of the nullary zero symbol.
`standardSentenceRoundtrip` uses the defining equations and quantifier-free
induction to prove the Foundation round trip up to biconditional.

The arithmetic import uses additive left cancellation from
`IPRADerivations.Core.Semiring` at Foundation's existing `PRALanguage.addCore`
symbol. The [PA194 export](../../../Computability/BusyBeaver/Research/PA/verification/pa194/ipra/native-endpoint/README.md#conciseipra-export)
uses the existing Foundation proof of the equivalence for the literal
194-state machine.

Build the bridge and the arithmetic test from the repository root.

```sh
lake build IPRABridge
lake build +IPRABridge.Checks.Arithmetic
lake build +IPRABridge.Checks.Roundtrip
lake build +IPRABridge.Checks.OpenSequents
lake build +IPRABridge.Checks.ScopedSequents
lake env lean --run Logic/PrimitiveRecursiveArithmetic/Bridge/check-import-closure.lean
```

The [Lean entry point](Lean/IPRABridge.lean) exposes closed and open transports.
The [symbol table](SYMBOLS.md) gives checked comparisons for existing Foundation
arithmetic codes and their shared Concise counterparts.

For finite PR codes and indexed argument lists, import
`DiophantineConsistency.PRAFiniteCodeSyntax`. For code, term and formula
translation, import `IPRABridge.Syntax`. The latter uses the equality-only
`IPRAReferenceLanguage` and the intuitionistic quantifier-free predicate from
`IPRAOpenSyntax`. The closure check sees 1,162 source modules for finite code
syntax, compared with 2,224 through the former evaluator import, and 2,366 for
syntax translation, down from 2,544. These counts include Lean and Mathlib
sources. Existing imports of `PRAFiniteFunctionCodes`, `PRATheory`,
`IPRAQuantifierFree` and `IPRAEqualityOnlyReference` still supply the original
declarations and their accompanying results.

## Choosing an iPRA interface

State new reusable arithmetic results in ordinary ConciseIPRA and place the
proofs in `IPRADerivations`. Use `Prf PRAAx Γ φ` for an open derivation whose
context and formula have the same finite scope. A closed theorem has
`Γ = []` and scope `0`. A typical use of an open result is additive
cancellation under hypotheses.

```lean
import IPRADerivations.Core.Semiring

open LeanProofs.ConciseIPRA
open scoped Fm

example {n : ℕ} {Γ : List (Fm PTm n)} {a b c : PTm n}
    (h : Prf PRAAx Γ ((a + b) ≐ (a + c))) : Prf PRAAx Γ (b ≐ c) :=
  LeanProofs.IPRA.add_left_cancel h
```

Use `DiophantineConsistency.IPRAStandardTheory.standardTheory` for new
Foundation iPRA endpoints. The same declaration is available from
`DiophantineConsistency.IPRAStandardAxioms` for files that need the theory
statement without the conversion proofs. Import `IPRABridge.Standard` when a file needs
only closed theorem transport. The umbrella import `IPRABridge` also exposes
that interface. A Foundation client can translate a closed Concise theorem
and then compare the translated symbols with the symbols it already uses.

```lean
import IPRABridge.Standard

open LO LO.FirstOrder LeanProofs.ConciseIPRA
open DiophantineConsistency.IPRAStandardTheory (standardTheory)

example {φ : Fm PTm 0} (h : Prf PRAAx [] φ) :
    standardTheory ⊢ IPRABridge.toStandardSentence φ :=
  IPRABridge.conciseToStandard h
```

For local hypotheses, use the [open transports](Lean/IPRABridge/OpenSequents.lean).
Use [scoped reflection](Lean/IPRABridge/ScopedSequents.lean) when the original
Foundation formulas are given in a common finite scope. Distinct labels
preserve the free-variable distinctions on the return trip. The
[open check](Lean/IPRABridge/Checks/OpenSequents.lean) uses compound argument
terms, parameterized induction, and existential elimination.

Foundation's `IPRANativeTheory.nativeTheory` names its candidate
axiomatization. ConciseIPRA's `NPrf` names the scalar calculus.
When using a result of classical PRA, HA, PA, or a fragment such as `IΣ₁`,
state that theory in the judgment and use the relevant checked transfer.
