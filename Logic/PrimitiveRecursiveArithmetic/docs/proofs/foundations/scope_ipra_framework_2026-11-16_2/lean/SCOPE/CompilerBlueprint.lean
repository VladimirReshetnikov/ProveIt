import SCOPE.Kernel
import SCOPE.BoundedCode

/-!
# SCOPE-iPRA: effect-typed compiler blueprint

This file records the intended host-side indexing.  The checked implementation
must return `Prf PRAAx` values; semantic `Nat` propositions are not accepted as
substitutes for object derivations.
-/

namespace LeanProofs.IPRA.SCOPE

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm

/-- What is permitted to cross a certificate scope. -/
inductive EscapeMode
  | sealed       -- no certificate-dependent public data
  | relational   -- only an existential/quotient observation relation
  | named        -- a concrete term; requires a direct producer or bounded selector
  deriving DecidableEq, Repr

/-- Static metadata used by the metalevel compiler and audit. -/
structure NodeMeta where
  label : String
  mode : EscapeMode
  producerBoundary : Option String := none
  hasFiniteBound : Bool := false
  hasCoherenceProof : Bool := false
  deriving Repr

/-!
A convenient final implementation can use a GADT of the following shape:

```
inductive Plan : {n : Nat} → List (Fm PTm n) → Fm PTm n → Type
  | exact (h : Γ ⊢[PRAAx] A) : Plan Γ A
  | specialize (p : Plan Γ A) (σ : Fin n → PTm m) :
      Plan (Γ.map (fun C => C.subst σ)) (A.subst σ)
  | supply (p : Plan Γ A)
      (s : ∀ C ∈ Γ, Plan Δ C) : Plan Δ A
  | seal (producer : Plan Γ (Fm.ex V))
      (consumer : Plan (V :: Γ.map Fm.shift) A.shift) : Plan Γ A
  | boundary (body : Plan (B :: Γ) A) : Plan Γ (B ⟶ A)
```

`compile : Plan Γ A → Γ ⊢[PRAAx] A` is structural recursion using exactly
`Prf.subst`, `Prf.trans`, `Prf.exE`, and `Prf.impI`.

The graph frontend assigns each certificate one of the three `EscapeMode`s.
* `sealed` compiles to `Plan.seal`;
* `relational` constructs an outer existential output relation and requires an
  exact, quotient, or metric coherence derivation;
* `named` is accepted only with a direct PR producer or a `SearchN` bound and
  existence derivation.

A normalization pass places each existential scope at the least region
containing all its consumers, removes dead nodes, and leaves exactly the
reachable unresolved producer formulas as outer boundaries.  Soundness is
then immediate from `compile`; scope safety is enforced by the arities of
`Plan.seal`.
-/

end LeanProofs.IPRA.SCOPE
