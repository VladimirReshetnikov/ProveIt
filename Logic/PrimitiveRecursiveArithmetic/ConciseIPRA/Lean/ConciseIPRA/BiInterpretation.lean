import ConciseIPRA.RoundTripPRA

/-!
# `T_eq` and `iPRA` are bi-interpretable

The scalar theory `T_eq` (zero, successor and the iterator binder, with the two
iterator equations, the cover axiom, `0 ≠ 1` and equation induction) and
intuitionistic primitive recursive arithmetic `iPRA` (a function symbol for
every primitive recursive definition, the defining equations, the successor
axioms and quantifier-free induction) are synonymous:

* `ToPRA.interp` translates `T_eq` into `iPRA`;
* `FromPRA.interp` translates `iPRA` into `T_eq`;
* both composites are provably the identity on terms, hence every formula is
  provably equivalent to its round trip.

Consequently each translation is faithful: a sequent is derivable in one theory
exactly when its translation is derivable in the other.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm

variable {n : ℕ}

/-- `T_eq` and `iPRA` are bi-interpretable. -/
def biInterp : BiInterp TeqAx PRAAx where
  F := ToPRA.interp
  G := FromPRA.interp
  gf t := Prf.eqSymm (RoundTrip.sigma_tau t)
  fg t := Prf.eqSymm (RoundTrip.tau_sigma t)

/-- The translation of `T_eq` into `iPRA` is faithful. -/
theorem teq_iff_pra {Γ : List (Fm Tm n)} {φ : Fm Tm n} :
    (Γ ⊢[TeqAx] φ) ↔
      (Γ.map (Fm.map fun _ => ToPRA.tau) ⊢[PRAAx] φ.map fun _ => ToPRA.tau) :=
  biInterp.iff

/-- The translation of `iPRA` into `T_eq` is faithful. -/
theorem pra_iff_teq {Γ : List (Fm PTm n)} {φ : Fm PTm n} :
    (Γ ⊢[PRAAx] φ) ↔
      (Γ.map (Fm.map fun _ => FromPRA.sigma) ⊢[TeqAx] φ.map fun _ => FromPRA.sigma) :=
  biInterp.symm.iff

/-- In `T_eq`, every formula is equivalent to its round trip through `iPRA`. -/
theorem teq_roundTrip (φ : Fm Tm n) (Γ : List (Fm Tm n)) :
    Γ ⊢[TeqAx] Fm.iff φ ((φ.map fun _ => ToPRA.tau).map fun _ => FromPRA.sigma) :=
  biInterp.roundTrip φ Γ

/-- In `iPRA`, every formula is equivalent to its round trip through `T_eq`. -/
theorem pra_roundTrip (φ : Fm PTm n) (Γ : List (Fm PTm n)) :
    Γ ⊢[PRAAx] Fm.iff φ ((φ.map fun _ => FromPRA.sigma).map fun _ => ToPRA.tau) :=
  biInterp.symm.roundTrip φ Γ

/-- Theorems of `T_eq` are exactly the formulas whose translations are theorems
of `iPRA`. -/
theorem teq_theorem_iff (φ : Fm Tm n) :
    ([] ⊢[TeqAx] φ) ↔ ([] ⊢[PRAAx] φ.map fun _ => ToPRA.tau) :=
  teq_iff_pra (Γ := [])

/-- Theorems of `iPRA` are exactly the formulas whose translations are theorems
of `T_eq`. -/
theorem pra_theorem_iff (φ : Fm PTm n) :
    ([] ⊢[PRAAx] φ) ↔ ([] ⊢[TeqAx] φ.map fun _ => FromPRA.sigma) :=
  pra_iff_teq (Γ := [])

/-- The two theories are equiconsistent. -/
theorem teq_consistent_iff :
    ([] ⊢[TeqAx] (Fm.bot : Fm Tm 0)) ↔ ([] ⊢[PRAAx] (Fm.bot : Fm PTm 0)) :=
  teq_theorem_iff Fm.bot

end LeanProofs.ConciseIPRA
