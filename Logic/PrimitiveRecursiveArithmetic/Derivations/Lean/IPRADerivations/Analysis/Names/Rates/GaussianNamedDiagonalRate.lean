import IPRADerivations.Analysis.Names.GaussianNameEquivalence

/-!
# Removing a finite same-clock comparison allowance

Two regular names with a dyadic same-clock error of any fixed
numerical multiple are equivalent at their original independent
observation precisions.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedDiagonalRate

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent point_at)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_through_diagonal)
open GaussianRationalSlackRemoval (precision slack_removal_at)
open GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def diagonalRate (f g : PR 2) (x y K : PTm n) : Fm PTm n :=
  .all (distanceBounded (ap2 f (var 0) (Syn.shift x)) (ap2 g (var 0) (Syn.shift y)) (Syn.shift K) (unit (var 0)))

ipra_subst diagonalRate [Syn.subst_shift, Syn.shift_subst]

theorem cross_at (f g : PR 2) (x y K p q : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hd : Γ ⊢[PRAAx] diagonalRate f g x y K) : Γ ⊢[PRAAx]
    distanceBounded (ap2 f p x) (ap2 g q y) (unit p+unit q) (unit p*unit q) := by
  let Z := qsub (ap2 f p x) (ap2 g q y)
  let A := unit p+unit q
  let B := unit p*unit q
  let C := K+two
  let t := precision Z A B C
  have hmid : Γ ⊢[PRAAx] distanceBounded (ap2 f t x) (ap2 g t y) K (unit t) := by
    simpa [diagonalRate] using hd.allE t
  exact slack_removal_at Z A B C (positive_product _ _ (unit_positive p) (unit_positive q))
    (distance_through_diagonal p q t K (point_at f x p t hf) hmid (point_at g y t q hg))

theorem cross_of_diagonal_rate (f g : PR 2) (x y K : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hd : Γ ⊢[PRAAx] diagonalRate f g x y K) : Γ ⊢[PRAAx] crossEquivalent f g x y := by
  let sh (z : PTm n) := Syn.shift (Syn.shift z)
  have hF : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointCN f (sh x) :=
    by simpa [Fm.shift,Syn.shift,sh] using hf.shift.shift
  have hG : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointCN g (sh y) :=
    by simpa [Fm.shift,Syn.shift,sh] using hg.shift.shift
  have hD : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] diagonalRate f g (sh x) (sh y) (sh K) :=
    by simpa [Fm.shift,Syn.shift,sh] using hd.shift.shift
  exact .allI (.allI (cross_at f g (sh x) (sh y) (sh K) (var 1) (var 0) hF hG hD))

theorem actual_named_diagonal_rate_equivalence_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (((pointCN f (var 0) ⋏ pointCN g (var 1)) ⋏ diagonalRate f g (var 0) (var 1) (var 2)) ⟶
        crossEquivalent f g (var 0) (var 1)) :=
  closeUniv 3 (.impI (cross_of_diagonal_rate f g _ _ _ Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₁.andE₂ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedDiagonalRate
