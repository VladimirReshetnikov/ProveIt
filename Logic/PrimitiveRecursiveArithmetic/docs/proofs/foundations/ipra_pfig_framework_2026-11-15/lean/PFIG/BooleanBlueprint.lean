import ConciseIPRA.PR

/-!
# Boolean reflection and bounded-search targets

This module fixes the object-level interfaces.  A complete implementation must
choose concrete PR definitions for Boolean equality, connectives, folds, and
state pairing, then fill the target proofs by `PRA.qfInd`.
-/

namespace LeanProofs.ConciseIPRA.PFIG.Boolean

open Syn
open scoped Fm

variable {n : Nat}

/-- The numeral one. -/
def one : PTm n := PTm.succ PTm.zero

/-- Object assertion that a numerical Boolean is true. -/
def IsTrue (b : PTm n) : Fm PTm n := b ≐ one

/-- Object assertion that a term is a Boolean. -/
def IsBool (b : PTm n) : Fm PTm n :=
  (b ≐ PTm.zero) ⋎ (b ≐ one)

/-- A Boolean code together with actual iPRA reflection. -/
structure BoolReflection (A : Fm PTm n) where
  code : PTm n
  range : ([] : List (Fm PTm n)) ⊢[PRAAx] IsBool code
  trueIff : ([] : List (Fm PTm n)) ⊢[PRAAx] Fm.iff (IsTrue code) A

/-- Main syntax-directed target: every QF formula has a reflected Boolean. -/
def BooleanizeQFTarget : Prop :=
  ∀ (n : Nat) (A : Fm PTm n), A.QF → Nonempty (BoolReflection A)

/-- A bounded search is specified by a bound term and a QF admissibility
formula.  The bound is included in `admissible` by the caller's chosen order
library, so this interface does not depend on a particular `<` definition. -/
structure SearchSpec (n : Nat) where
  bound : PTm n
  admissible : Fm PTm (n + 1)
  qf : admissible.QF

/-- Result of compiling least bounded search under an arbitrary context. -/
structure SearchResult {n : Nat} (S : SearchSpec n)
    (Γ : List (Fm PTm n)) where
  witness : PTm n
  sound : Γ ⊢[PRAAx] Fm.ex S.admissible →
    Γ ⊢[PRAAx] S.admissible.subst (inst witness)
  /-- `minimalFormula` is supplied by the order library and says that no
  smaller admissible witness exists. -/
  minimalFormula : Fm PTm n
  minimal : Γ ⊢[PRAAx] Fm.ex S.admissible →
    Γ ⊢[PRAAx] minimalFormula

/-- Main least-search compiler target. -/
def LeastSearchTarget : Prop :=
  ∀ (n : Nat) (S : SearchSpec n) (Γ : List (Fm PTm n)),
    Nonempty (SearchResult S Γ)

/-- A reflected finite fold.  `stepFormula` specifies the intended update of
an accumulator; all state validity is QF. -/
structure FoldReflection {n : Nat}
    (Init : PTm n) (Step : PTm (n + 2))
    (Inv : Fm PTm (n + 2)) where
  qf : Inv.QF
  base : ([] : List (Fm PTm n)) ⊢[PRAAx]
    Inv.subst (Fin.cases Init (Fin.cases PTm.zero var))
  preserve : Inv :: ([] : List (Fm PTm (n + 2))) ⊢[PRAAx]
    Inv  -- schematic target; replace by instantiated successor invariant

/-- Equality stability is the first consumer of QF Booleanization. -/
theorem equalityStability_target (s t : PTm n) :
    ([] : List (Fm PTm n)) ⊢[PRAAx]
      (((s ≐ t) ⟶ Fm.bot) ⟶ Fm.bot) ⟶ (s ≐ t) := by
  -- Parenthesization must be replaced by an explicit `negFormula` helper in
  -- the integrated file.  Proof: decide equality with its reflected Boolean.
  sorry

end LeanProofs.ConciseIPRA.PFIG.Boolean
