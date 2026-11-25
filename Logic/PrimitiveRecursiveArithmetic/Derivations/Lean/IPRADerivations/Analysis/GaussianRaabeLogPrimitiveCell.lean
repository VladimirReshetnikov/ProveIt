import IPRADerivations.Analysis.GaussianNamedDifferenceAlgebra
import IPRADerivations.Analysis.GaussianPositiveRationalLogarithmIncrement
import IPRADerivations.Analysis.GaussianRationalPowerDifference
import IPRADerivations.Analysis.GaussianStirlingOddCoefficients

/-!
# A finite cell for the positive logarithm primitive

The endpoints use the original logarithm observations at the same
clock. The error in the left-rectangle area is quadratic in the
cell width, with an explicit observation allowance.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianRaabeLogPrimitiveCell

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (normSq normSq_one normSq_scale oneCode scale)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianPositiveRationalLogarithm (fraction sample)
open GaussianPositiveRationalLogarithmIncrement (increment original_increment)
open GaussianRationalDistanceOrder (distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (ofGaussian_canonical ofGaussian_represents positive_product qadd qmul qzero)
open GaussianRationalMetric (bounded bounded_of_cleared distanceBounded qsub)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalSyntheticDivision (qadd_congr qadd_sub_cancel qmul_congr qsub_congr)
open GaussianStirlingOddCoefficients (fraction_add_same fraction_equal fraction_product)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def primitive (p A D : PTm n) : PTm n := qsub (qmul (fraction A D) (sample p A D)) (fraction A D)

def area (p A D H : PTm n) : PTm n := qmul (fraction H D) (sample p A D)

def numerator (p A H : PTm n) : PTm n := (two*A+H)*(H*H)*unit p+two*(A+H)*(A*A)

def denominator (p A D : PTm n) : PTm n := D*(A*A)*unit p

@[simp] theorem subst_primitive {m : ℕ} (σ : Fin n → PTm m) (p A D : PTm n) :
    Syn.subst σ (primitive p A D) = primitive (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ D) := by
  simp [primitive]

@[simp] theorem subst_area {m : ℕ} (σ : Fin n → PTm m) (p A D H : PTm n) :
    Syn.subst σ (area p A D H) = area (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ D) (Syn.subst σ H) := by
  simp [area]

theorem fraction_bound (A D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] bounded (fraction A D) A D := by
  have e : Γ ⊢[PRAAx] normSq (scale A oneCode) ≐ A*A :=
    (normSq_scale _ _).eqTrans ((congrMul (.eqRefl _) normSq_one).eqTrans (by ipra_ring))
  exact bounded_of_cleared _ _ D _ D hD hD (ofGaussian_represents _ _ hD)
    (le_congr (congrMul (.eqRefl _) e).eqSymm (by ipra_ring) (le_refl ((D*D)*(A*A))))

theorem fraction_difference (A H D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] qsub (fraction (A+H) D) (fraction A D) ≐ fraction H D :=
  (qsub_congr (fraction_add_same A H D hD).eqSymm (.eqRefl _)).eqTrans
    (qadd_sub_cancel _ _ (ofGaussian_canonical _ _ hD))

private theorem relative_defect (p A D H : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] qsub (qsub (primitive p (A+H) D) (primitive p A D)) (area p A D H) ≐
      qsub (qmul (fraction (A+H) D) (increment p p A D H)) (fraction H D) := by
  let y := fraction (A+H) D
  let x := fraction A D
  let h := fraction H D
  let b := sample p (A+H) D
  let a := sample p A D
  let t := qmul h a
  let v := qmul y (qsub b a)
  have ep : Γ ⊢[PRAAx] qsub (qmul y b) (qmul x a) ≐ qadd t v :=
    (qsub_congr (GaussianRationalPowerAlgebra.qmul_commutative y b)
      (GaussianRationalPowerAlgebra.qmul_commutative x a)).eqTrans
      ((GaussianRationalPowerDifference.product_difference b a y x).eqTrans
        ((qadd_congr (GaussianRationalPowerAlgebra.qmul_commutative (qsub b a) y)
          (qmul_congr (.eqRefl a) (fraction_difference A H D hD))).eqTrans
          ((qadd_congr (.eqRefl v) (GaussianRationalPowerAlgebra.qmul_commutative a h)).eqTrans
            (GaussianReciprocalHorner.qadd_commutative v t))))
  have move : Γ ⊢[PRAAx] qsub (primitive p (A+H) D) (primitive p A D) ≐ qsub (qadd t v) h :=
    (GaussianNamedDifferenceAlgebra.rational_shuffle (qmul y b) y (qmul x a) x).eqTrans
      (qsub_congr ep (fraction_difference A H D hD))
  have et := GaussianRationalReconstruction.qsub_zero_right (Γ := Γ) t (GaussianRationalHorner.qmul_canonical _ _)
  have eh := GaussianRationalReconstruction.qsub_zero_right h (ofGaussian_canonical _ _ hD)
  have ec := qadd_sub_cancel (Γ := Γ) t v (GaussianRationalHorner.qmul_canonical _ _)
  exact (qsub_congr move et.eqSymm).eqTrans
    ((GaussianNamedDifferenceAlgebra.rational_shuffle (qadd t v) h t qzero).eqTrans
      (qsub_congr ec eh))

private theorem relative_bias (A D H : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] distanceBounded (qmul (fraction (A+H) D) (fraction H A)) (fraction H D) (H*H) (D*A) := by
  let E := D*A
  have hE := positive_product D A hD hA
  have e₁ : Γ ⊢[PRAAx] qmul (fraction (A+H) D) (fraction H A) ≐ fraction (H*A+H*H) E :=
    (fraction_product _ _ _ _ hD hA).eqTrans
      (GaussianCompactRiemannName.fraction_congr _ _ _ _ (by ipra_ring) (.eqRefl E))
  have e₂ : Γ ⊢[PRAAx] fraction H D ≐ fraction (H*A) E :=
    fraction_equal _ _ _ _ hD hE (by dsimp only [E]; ipra_ring)
  have e := (qsub_congr e₁ e₂).eqTrans (fraction_difference (H*A) (H*H) E hE)
  exact bound_congr e.eqSymm (.eqRefl _) (.eqRefl _) (fraction_bound (H*H) E hE)

theorem cell_error (p A D H : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] distanceBounded (qsub (primitive p (A+H) D) (primitive p A D))
      (area p A D H) (numerator p A H) (denominator p A D) := by
  let U := unit p
  let y := fraction (A+H) D
  let c := fraction H A
  let v := increment p p A D H
  let S := A*A*U
  let W := D*S
  have hU := unit_positive (Γ := Γ) p
  have ha := positive_product A A hA hA
  have hS := positive_product _ _ ha hU
  have hW := positive_product _ _ hD hS
  have hE := positive_product D A hD hA
  have first : Γ ⊢[PRAAx] distanceBounded v c (H*H*U+two*(A*A)) S :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ ha (positive_product _ _ hU hU)) hS
      (le_of_eq_add (d := zero) (by dsimp only [U,S,GaussianPositiveRationalLogarithmIncrement.errorNumerator,
        GaussianPositiveRationalLogarithmIncrement.errorDenominator]; ipra_ring))
      (original_increment p p A D H hA hD)
  have scaled : Γ ⊢[PRAAx] distanceBounded (qmul y v) (qmul y c) ((A+H)*(H*H*U+two*(A*A))) W :=
    bound_congr (GaussianRationalRoundedPower.multiplication_difference y v c).eqSymm
      (.eqRefl _) (.eqRefl _) (bounded_product _ _ _ _ _ _ hD hS (fraction_bound (A+H) D hD) first)
  have bias : Γ ⊢[PRAAx] distanceBounded (qmul y c) (fraction H D) (H*H*A*U) W :=
    distance_radius_mono _ _ _ _ _ _ hE hW
      (le_of_eq_add (d := zero) (by dsimp only [W,S]; ipra_ring)) (relative_bias A D H hA hD)
  exact bound_congr (relative_defect p A D H hD).eqSymm (by dsimp only [numerator]; ipra_ring)
    (by dsimp only [W,S,denominator]; ipra_ring)
    (distance_triangle_same (qmul y v) (qmul y c) (fraction H D) _ _ W hW scaled bias)

theorem actual_positive_logarithm_primitive_cell_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (let p := var 0
       let A := var 1
       let D := var 2
       let H := var 3
       (le one A ⋏ le one D) ⟶ distanceBounded
         (qsub (primitive p (A+H) D) (primitive p A D)) (area p A D H) (numerator p A H) (denominator p A D)) :=
  closeUniv 4 (.impI (cell_error _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRaabeLogPrimitiveCell
