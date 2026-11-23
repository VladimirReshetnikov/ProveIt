import IPRADerivations.Core.Tactic

/- Candidate object-theory derivations, for the pinned ProveIt root.
   Variables of type ZT are differences of natural-number terms.
   This file has no sorry or added axioms. See README for build status. -/

namespace LeanProofs.IPRA.Knots
open LeanProofs.ConciseIPRA
open scoped Fm

def fox {n} (x y : ZT n) : ZT n := (y + y) - x

def aff {n} (t x y : ZT n) : ZT n := t * x + (1 - t) * y

theorem foxIdem {n} {Γ : List (Fm PTm n)} (x : ZT n) :
    Γ ⊢[PRAAx] (fox x x).eq x := by
  unfold fox
  ipra_ring

theorem foxCancel {n} {Γ : List (Fm PTm n)} (x y : ZT n) :
    Γ ⊢[PRAAx] (fox (fox x y) y).eq x := by
  unfold fox
  ipra_ring

def foxTriangle {n} (x y z : ZT n) : Fm PTm n :=
  (fox (fox x y) z).eq (fox (fox x z) (fox y z))

theorem foxTriangleOpen {n} {Γ : List (Fm PTm n)} (x y z : ZT n) :
    Γ ⊢[PRAAx] foxTriangle x y z := by
  unfold foxTriangle fox
  ipra_ring

def foxTriangleClosed : Fm PTm 0 :=
  univ 6 (foxTriangle (.var2 0 1) (.var2 2 3) (.var2 4 5))

theorem foxTriangleDerivation :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] foxTriangleClosed :=
  closeUniv 6 (foxTriangleOpen _ _ _)

theorem affTriangle {n} {Γ : List (Fm PTm n)} (t x y z : ZT n) :
    Γ ⊢[PRAAx] (aff t (aff t x y) z).eq (aff t (aff t x z) (aff t y z)) := by
  unfold aff
  ipra_ring

-- Reversing the parameter in the affine crossing. If s*t=1 the
-- right side of this identity is x, by substitution in the object theory.
theorem affBack {n} {Γ : List (Fm PTm n)} (s t x y : ZT n) :
    Γ ⊢[PRAAx] (aff s (aff t x y) y).eq (x + (s*t - 1)*(x-y)) := by
  unfold aff
  ipra_ring

-- The signed difference used in the two-braid recurrence.
theorem braidDifference {n} {Γ : List (Fm PTm n)} (t x y : ZT n) :
    Γ ⊢[PRAAx] (aff t y x - x).eq (t * (y - x)) := by
  unfold aff
  ipra_ring

end LeanProofs.IPRA.Knots
