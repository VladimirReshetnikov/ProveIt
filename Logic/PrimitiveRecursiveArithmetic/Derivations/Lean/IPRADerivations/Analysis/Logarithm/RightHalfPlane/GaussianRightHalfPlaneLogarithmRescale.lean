import IPRADerivations.Analysis.Logarithm.RightHalfPlane.GaussianRightHalfPlaneLogarithm

/-!
# Exact rescaling of the right-half-plane logarithm

The radial logarithm is invariant under the squared common factor,
and the argument depends only on the ratio of the two numerators.
For an Euler row, extract the real logarithm of the positive integer
index while preserving its imaginary sign and original numerator.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneLogarithmRescale

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianPositiveRationalLogarithm (logF name_regular)
open GaussianRationalHorner (positive_product)
open GaussianRightHalfPlaneLogarithm (source nameF data)
open GaussianRightHalfPlaneRadialLogarithm (normNum normDen log_source)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "RF" => GaussianRightHalfPlaneRadialLogarithm.nameF
local notation "AF" => GaussianRightHalfPlaneArgument.nameF
local notation "R" => GaussianRightHalfPlaneRadialLogarithm.data
local notation "P" => GaussianRightHalfPlaneArgument.data
local notation "L" => GaussianPositiveRationalLogarithm.data

private theorem source_rescale (A D neg k : PTm n) (h : Γ ⊢[PRAAx] source A D neg)
    (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx] source (k*A) (k*D) neg :=
  .andI (.andI (positive_product k A hk h.andE₁.andE₁) h.andE₁.andE₂)
    (positive_product k D hk h.andE₂)

private theorem radial_rescale (A B D neg k : PTm n) (h : Γ ⊢[PRAAx] source A D neg)
    (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] crossEquivalent RF RF (R (k*A) (k*B) (k*D)) (R A B D) := by
  have hs := source_rescale A D neg k h hk
  have hu := log_source (k*A) (k*B) (k*D) hs.andE₁.andE₁ hs.andE₂
  have hv := log_source A B D h.andE₁.andE₁ h.andE₂
  let a := normNum (k*A) (k*B)
  let b := normDen (k*D)
  let c := normNum A B
  let d := normDen D
  have value := GaussianPositiveRationalLogarithmProperness.original_logarithm_proper a b c d hu hv
    (by dsimp [a,b,c,d,normNum,normDen]; ipra_ring)
  exact GaussianNamedHalf.proper logF logF (L a b) (L c d)
    (name_regular a b hu) (name_regular c d hv) value

theorem rescale (A B D neg k : PTm n) (h : Γ ⊢[PRAAx] source A D neg)
    (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] crossEquivalent nameF nameF (data (k*A) (k*B) (k*D) neg) (data A B D neg) := by
  have hs := source_rescale A D neg k h hk
  have axis := radial_rescale A B D neg k h hk
  have phase := GaussianRightHalfPlaneArgumentProperness.equal_ratio (k*A) (k*B) A B neg
    hs.andE₁ h.andE₁.andE₁ (by ipra_ring)
  exact add_cross RF RF AF AF (R (k*A) (k*B) (k*D)) (R A B D) (P (k*A) (k*B) neg) (P A B neg)
    (GaussianRightHalfPlaneRadialLogarithm.regular (k*A) (k*B) (k*D) hs.andE₁.andE₁ hs.andE₂)
    (GaussianRightHalfPlaneRadialLogarithm.regular A B D h.andE₁.andE₁ h.andE₂)
    (GaussianRightHalfPlaneArgument.name_regular (k*A) (k*B) neg hs.andE₁)
    (GaussianRightHalfPlaneArgument.name_regular A B neg h.andE₁) axis phase

private theorem denominator_congr (A B D E neg : PTm n) (h : Γ ⊢[PRAAx] D ≐ E) :
    Γ ⊢[PRAAx] data A B D neg ≐ data A B E neg := by
  simpa [GaussianRightHalfPlaneLogarithm.subst_data,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (data (var 0) (var 1) (var 2) (var 3) : PTm 4)
      (σ := ![A,B,D,neg]) (σ' := ![A,B,E,neg])
      (fun i => by fin_cases i <;> first | exact .eqRefl _ | exact h)

private theorem cross_same_data (x y : PTm n) (hx : Γ ⊢[PRAAx] pointCN nameF x)
    (h : Γ ⊢[PRAAx] x ≐ y) : Γ ⊢[PRAAx] crossEquivalent nameF nameF x y := by
  have e := Prf.eqSubst (Γ := Γ) (Ax := PRAAx) (crossEquivalent nameF nameF (var 0) (var 1) : Fm PTm 2)
    ![x,x] ![x,y] (fun i => by fin_cases i <;> first | exact .eqRefl _ | exact h)
    (by simpa only [GaussianNameEquivalence.subst_crossEquivalent,Syn.subst_var,
      Matrix.cons_val_zero,Matrix.cons_val_one] using cross_refl nameF x hx)
  simpa only [GaussianNameEquivalence.subst_crossEquivalent,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one] using e

theorem split_denominator (A B D neg k : PTm n) (h : Γ ⊢[PRAAx] source A D neg)
    (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] crossEquivalent nameF (addF logF nameF) (data A B D neg)
      (addData (L k one) (data A B (D*k) neg)) := by
  let y := data (k*A) (k*B) (k*D) neg
  let z := data (k*A) (k*B) (one*(D*k)) neg
  have hy := GaussianRightHalfPlaneLogarithm.regular (k*A) (k*B) (k*D) neg (source_rescale A D neg k h hk)
  have e := denominator_congr (Γ := Γ) (k*A) (k*B) (k*D) (one*(D*k)) neg (by ipra_ring)
  have align := cross_same_data y z hy e
  have scaledSource : Γ ⊢[PRAAx] source A (D*k) neg := .andI h.andE₁ (positive_product D k h.andE₂ hk)
  have scale := GaussianRightHalfPlaneLogarithm.positive_scaling A B (D*k) neg k one scaledSource
    (.andI hk (le_refl one))
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (rescale A B D neg k h hk))
    (cross_trans _ _ _ _ _ _ align scale)

theorem split_shift (A B D neg k : PTm n) (h : Γ ⊢[PRAAx] source A D neg)
    (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] crossEquivalent nameF (addF logF nameF) (data (A+k*D) B D neg)
      (addData (L k one) (data (A+k*D) B (D*k) neg)) := by
  have hs : Γ ⊢[PRAAx] source (A+k*D) D neg :=
    .andI (.andI (le_trans h.andE₁.andE₁ (le_add_right _ _)) h.andE₁.andE₂) h.andE₂
  exact split_denominator (A+k*D) B D neg k hs hk

theorem actual_right_half_plane_logarithm_rescale_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 2) (var 3) ⟶ le one (var 4) ⟶
      crossEquivalent nameF nameF (data (var 4*var 0) (var 4*var 1) (var 4*var 2) (var 3))
        (data (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 5 (.impI (.impI (rescale _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_right_half_plane_logarithm_shift_split_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 2) (var 3) ⟶ le one (var 4) ⟶
      crossEquivalent nameF (addF logF nameF) (data (var 0+var 4*var 2) (var 1) (var 2) (var 3))
        (addData (L (var 4) one) (data (var 0+var 4*var 2) (var 1) (var 2*var 4) (var 3)))) :=
  closeUniv 5 (.impI (.impI (split_shift _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneLogarithmRescale
