import IPRADerivations.Analysis.GaussianNameEquivalence

/-!
# Removing a finite same-clock comparison allowance

Two regular names with a dyadic same-clock error of any fixed
numerical multiple are equivalent at their original independent
observation precisions.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedDiagonalRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent point_at)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalSlackRemoval (precision slack_removal_at)
open GaussianRationalHorner (positive_product)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def diagonalRate (f g : PR 2) (x y K : PTm n) : Fm PTm n :=
  .all (distanceBounded (ap2 f (var 0) (Syn.shift x)) (ap2 g (var 0) (Syn.shift y)) (Syn.shift K) (unit (var 0)))

@[simp] theorem subst_diagonalRate {m : ℕ} (σ : Fin n → PTm m) (f g : PR 2) (x y K : PTm n) :
    (diagonalRate f g x y K).subst σ = diagonalRate f g (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ K) := by
  simp [diagonalRate,Syn.subst_shift,Syn.shift_subst]

theorem cross_at (f g : PR 2) (x y K p q : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hd : Γ ⊢[PRAAx] diagonalRate f g x y K) : Γ ⊢[PRAAx]
    distanceBounded (ap2 f p x) (ap2 g q y) (unit p+unit q) (unit p*unit q) := by
  let Z := qsub (ap2 f p x) (ap2 g q y)
  let A := unit p+unit q
  let B := unit p*unit q
  let C := K+two
  let t := precision Z A B C
  let P := unit p
  let Q := unit q
  let T := unit t
  have hP : Γ ⊢[PRAAx] le one P := unit_positive p
  have hQ : Γ ⊢[PRAAx] le one Q := unit_positive q
  have hT : Γ ⊢[PRAAx] le one T := unit_positive t
  have hB : Γ ⊢[PRAAx] le one B := positive_product _ _ hP hQ
  have hPT := positive_product P T hP hT
  have hTQ := positive_product T Q hT hQ
  have hmid : Γ ⊢[PRAAx] distanceBounded (ap2 f t x) (ap2 g t y) K T := by
    simpa [diagonalRate] using hd.allE t
  have step := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ hPT hT (point_at f x p t hf) hmid
  have hStep := positive_product (P*T) T hPT hT
  have joined := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ hStep hTQ step (point_at g y t q hg)
  apply slack_removal_at Z A B C hB
  change Γ ⊢[PRAAx] distanceBounded (ap2 f p x) (ap2 g q y) (A*T+C*B) (B*T)
  exact distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ hStep hTQ) (positive_product _ _ hB hT)
    (le_of_eq_add (d := zero) (by dsimp only [A,B,C,P,Q,T]; ipra_ring)) joined

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
