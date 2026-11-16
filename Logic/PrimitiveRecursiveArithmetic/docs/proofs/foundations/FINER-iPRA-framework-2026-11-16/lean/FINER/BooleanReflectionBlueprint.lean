import FINER.KernelWrappers
import IPRADerivations.Core.MultiSums

/-!
# Bounded Boolean reflection: source-oriented blueprint

This file gives a syntactically explicit target API.  It is not claimed to have
been elaborated in the pinned ProveIt checkout.  Every unfinished proof is a
visible `sorry`; there are no hidden theorem-specific axioms.

The compiler is metalevel structural recursion on a *fixed* bounded formula.
It does not define or assume an object-level universal primitive-recursive
evaluator.
-/

namespace LeanProofs.IPRA.FINER

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

/-- Small theorem-specialised bounded syntax.  Bounds are terms in the outer
context; a bounded body has one additional variable at index zero. -/
inductive FixedBoundedFormula : (n : ℕ) → Type
  | eq {n} (a b : PTm n) : FixedBoundedFormula n
  | lt {n} (a b : PTm n) : FixedBoundedFormula n
  | and {n} (p q : FixedBoundedFormula n) : FixedBoundedFormula n
  | or {n} (p q : FixedBoundedFormula n) : FixedBoundedFormula n
  | imp {n} (p q : FixedBoundedFormula n) : FixedBoundedFormula n
  | bex {n} (bound : PTm n) (body : FixedBoundedFormula (n + 1)) :
      FixedBoundedFormula n
  | ball {n} (bound : PTm n) (body : FixedBoundedFormula (n + 1)) :
      FixedBoundedFormula n

/-- A Boolean term together with the object formula it reflects. -/
structure ReflectedPredicate (n : ℕ) where
  bit : PTm n
  formula : Fm PTm n
  bit01 : ∀ {Γ : List (Fm PTm n)},
    Γ ⊢[PRAAx] (bit ≐ zero) ⋎ (bit ≐ succ zero)
  sound1 : ∀ {Γ : List (Fm PTm n)},
    Γ ⊢[PRAAx] (bit ≐ succ zero) ⟶ formula
  complete1 : ∀ {Γ : List (Fm PTm n)},
    Γ ⊢[PRAAx] formula ⟶ (bit ≐ succ zero)
  sound0 : ∀ {Γ : List (Fm PTm n)},
    Γ ⊢[PRAAx] (bit ≐ zero) ⟶ neg formula
  complete0 : ∀ {Γ : List (Fm PTm n)},
    Γ ⊢[PRAAx] neg formula ⟶ (bit ≐ zero)

/-- Reflection of a fixed equality atom, using checked `eqb`. -/
def reflectEq {n : ℕ} (a b : PTm n) : ReflectedPredicate n := by
  -- bit := eqb a b; split with `eq_or_ne`; use `eqb_of_eq/eqb_of_ne`.
  sorry

/-- Reflection of the repository order formula. -/
def reflectLt {n : ℕ} (a b : PTm n) : ReflectedPredicate n := by
  -- Reuse `Core.Order` and equality/monus reflection.
  sorry

/-- Boolean conjunction; a convenient bit is multiplication. -/
def reflectAnd {n : ℕ} (p q : ReflectedPredicate n) :
    ReflectedPredicate n := by
  sorry

/-- Boolean disjunction; use sign of the sum or an equivalent checked bit. -/
def reflectOr {n : ℕ} (p q : ReflectedPredicate n) :
    ReflectedPredicate n := by
  sorry

/-- Decidable implication.  Reflection of `p` provides the finite case split
needed to prove `(p → q) ↔ (¬p ∨ q)` intuitionistically. -/
def reflectImp {n : ℕ} (p q : ReflectedPredicate n) :
    ReflectedPredicate n := by
  sorry

/-- Bounded existential compiled to a finite Boolean fold or to a checked
least-search adapter. -/
def reflectBoundedExists {n : ℕ}
    (bound : PTm n) (body : ReflectedPredicate (n + 1)) :
    ReflectedPredicate n := by
  sorry

/-- Bounded universal compiled as absence of a reflected counterexample, or as
an all-bit finite product. -/
def reflectBoundedForall {n : ℕ}
    (bound : PTm n) (body : ReflectedPredicate (n + 1)) :
    ReflectedPredicate n := by
  sorry

/-- Main compiler target. -/
def reflect : {n : ℕ} → FixedBoundedFormula n → ReflectedPredicate n
  | _, .eq a b => reflectEq a b
  | _, .lt a b => reflectLt a b
  | _, .and p q => reflectAnd (reflect p) (reflect q)
  | _, .or p q => reflectOr (reflect p) (reflect q)
  | _, .imp p q => reflectImp (reflect p) (reflect q)
  | _, .bex bound body => reflectBoundedExists bound (reflect body)
  | _, .ball bound body => reflectBoundedForall bound (reflect body)

end LeanProofs.IPRA.FINER
