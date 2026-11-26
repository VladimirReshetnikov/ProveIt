import IPRADerivations.Analysis.Gamma.GaussianGammaDensityMomentName
import IPRADerivations.Analysis.Names.Rates.GaussianNamedDifferenceQuotientProperness

/-!
# Normalization, mean and variance of the actual Gamma-density moment names

The zero/first/second instances of the literal density-grid moment
program give 1, x and x(x+1). The actual normalized name arithmetic
M2-M1*M1 consequently has value x. Positive real inputs are included;
the source-derived algebra holds throughout the original right half-plane.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDensityMeanVariance

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIntegralGammaIdentification (source)
open GaussianGammaRepeatedShift (risingProduct prefix_zero prefix_succ)
open GaussianGammaEulerHeadShift (linear)
open GaussianRationalHorner (qmul qadd ofGaussian canonical)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr qadd_congr qadd_sub_cancel qone)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_at)
open GaussianEuclideanDistanceName (pointCN)
open GaussianCoefficientNameBounds (unit)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "M" => GaussianGammaDensityMomentName.nameF

theorem linear_zero (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] linear z B zero ≐ ofGaussian z B :=
  GaussianRationalHorner.canonical_unique _ _ _ _ (GaussianRationalHorner.ofGaussian_canonical _ _ hB)
    (GaussianRationalHorner.ofGaussian_canonical _ _ hB) hB
    (GaussianRationalHorner.represents_congr (.eqRefl _) (GaussianGammaEulerHeadLower.translated_zero z B) (.eqRefl _)
      (GaussianRationalHorner.ofGaussian_represents _ _ hB)) (GaussianRationalHorner.ofGaussian_represents _ _ hB)

theorem linear_one (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    linear z B one ≐ qadd (ofGaussian z B) qone := by
  have right := GaussianRationalHorner.qadd_represents _ _ _ _ _ hB
    (GaussianRationalHorner.ofGaussian_represents z B hB) (GaussianRationalReciprocal.qone_represents_scaled B)
  have native : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (GaussianGammaEulerHeadLower.translated z B one)
      (ComplexLogarithmRemainder.add z (ComplexLogarithmRemainder.scale B ComplexLogarithmRemainder.oneCode)) := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [GaussianGammaEulerHeadLower.translated,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,
        GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale]
    all_goals (ipra_simps; ring)
  exact GaussianRationalHorner.canonical_unique _ _ _ _ (GaussianRationalHorner.ofGaussian_canonical _ _ hB)
    (GaussianRationalHorner.qadd_canonical _ _) hB
    (GaussianRationalHorner.represents_congr (.eqRefl _) native (.eqRefl _)
      (GaussianRationalHorner.ofGaussian_represents _ _ hB)) right

theorem prefix_one (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    risingProduct z B one ≐ ofGaussian z B :=
  (prefix_succ z B zero).eqTrans ((qmul_congr (prefix_zero z B) (linear_zero z B hB)).eqTrans
    ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
      (GaussianReciprocalHorner.qmul_one_right _ (GaussianRationalHorner.ofGaussian_canonical _ _ hB))))
theorem prefix_two (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    risingProduct z B two ≐ qmul (ofGaussian z B) (qadd (ofGaussian z B) qone) :=
  (prefix_succ z B one).eqTrans (qmul_congr (prefix_one z B hB) (linear_one z B hB))

theorem variance_literal (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qsub (risingProduct z B two) (qmul (risingProduct z B one) (risingProduct z B one)) ≐ ofGaussian z B := by
  let x := ofGaussian z B
  have hx := GaussianRationalHorner.ofGaussian_canonical (Γ := Γ) z B hB
  have expand : Γ ⊢[PRAAx] qmul x (qadd x qone) ≐ qadd (qmul x x) x :=
    (GaussianRationalCoefficientScaling.qmul_add x x qone).eqTrans
      (qadd_congr (.eqRefl _) (GaussianReciprocalHorner.qmul_one_right x hx))
  exact (qsub_congr (prefix_two z B hB) (qmul_congr (prefix_one z B hB) (prefix_one z B hB))).eqTrans
    ((qsub_congr expand (.eqRefl _)).eqTrans (qadd_sub_cancel (qmul x x) x hx))

theorem normalization (z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    crossEquivalent M constantF (GaussianGammaDensityMomentName.data z R B A zero) qone :=
  cross_trans _ _ _ _ _ _ (GaussianGammaDensityMomentName.original_integer_moment z R B A zero h)
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ (prefix_zero z B))
theorem mean (z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    crossEquivalent M constantF (GaussianGammaDensityMomentName.data z R B A one) (ofGaussian z B) :=
  cross_trans _ _ _ _ _ _ (GaussianGammaDensityMomentName.original_integer_moment z R B A one h)
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ (prefix_one z B h.andE₁.andE₂.andE₁.andE₁))
theorem second_moment (z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    crossEquivalent M constantF (GaussianGammaDensityMomentName.data z R B A two)
      (qmul (ofGaussian z B) (qadd (ofGaussian z B) qone)) :=
  cross_trans _ _ _ _ _ _ (GaussianGammaDensityMomentName.original_integer_moment z R B A two h)
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ (prefix_two z B h.andE₁.andE₂.andE₁.andE₁))

def varianceF : PR 2 := GaussianNamedDifference.nameF M (multiplyF M M)
def varianceData (z R B A : PTm n) : PTm n := GaussianNamedDifference.data
  (GaussianGammaDensityMomentName.data z R B A two)
  (multiplyData M M (GaussianGammaDensityMomentName.data z R B A one) (GaussianGammaDensityMomentName.data z R B A one))
@[simp] theorem subst_varianceData {m : ℕ} (σ : Fin n → PTm m) (z R B A : PTm n) :
    Syn.subst σ (varianceData z R B A) = varianceData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) := by simp [varianceData]

theorem variance_regular (z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    pointCN varianceF (varianceData z R B A) :=
  GaussianNamedDifference.name_regular _ _ _ _ (GaussianGammaDensityMomentName.name_regular z R B A two h)
    (multiply_fast _ _ _ _ (GaussianGammaDensityMomentName.name_regular z R B A one h)
      (GaussianGammaDensityMomentName.name_regular z R B A one h))

private theorem constant_difference (x y : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianNamedDifference.nameF constantF constantF) constantF (GaussianNamedDifference.data x y) (qsub x y) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 6)
    (GaussianNamedDifference.name_regular _ _ _ _ (constant_regular _) (constant_regular _)) (constant_regular _)
  refine .allI ?_
  have raw := GaussianNamedDifference.sample_error (Γ := Γ.map Fm.shift) constantF constantF (Syn.shift x) (Syn.shift y) (var 0)
    (constant_regular _) (constant_regular _)
  have actual := distance_congr (.eqRefl _)
    ((qsub_congr (constant_at _ _) (constant_at _ _)).eqTrans (constant_at (var 0) (qsub (Syn.shift x) (Syn.shift y))).eqSymm)
    (.eqRefl _) (.eqRefl _) raw
  simpa only [GaussianNamedDifference.subst_data,GaussianRationalMetric.subst_qsub,PTm.subst_num,Syn.shift] using actual

theorem variance (z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    crossEquivalent varianceF constantF (varianceData z R B A) (ofGaussian z B) := by
  let x := GaussianGammaDensityMomentName.data z R B A one
  let y := GaussianGammaDensityMomentName.data z R B A two
  let u := risingProduct z B one
  let v := risingProduct z B two
  have hx := GaussianGammaDensityMomentName.name_regular z R B A one h
  have hy := GaussianGammaDensityMomentName.name_regular z R B A two h
  have hu := constant_regular (Γ := Γ) u
  have hv := constant_regular (Γ := Γ) v
  have ex := GaussianGammaDensityMomentName.original_integer_moment z R B A one h
  have ey := GaussianGammaDensityMomentName.original_integer_moment z R B A two h
  have square := GaussianGammaAdjacentCutoff.multiply_cross M constantF M constantF x u x u hx hu hx hu ex ex
  have bound := cross_trans _ _ _ _ _ _ square (GaussianGammaWeierstrassApproximant.constant_product_cross u u)
  have diff := GaussianNamedDifferenceQuotientProperness.difference_proper M constantF (multiplyF M M) constantF y v
    (multiplyData M M x x) (qmul u u) hy hv (multiply_fast _ _ _ _ hx hx) (constant_regular _) ey bound
  exact cross_trans _ _ _ _ _ _ diff (cross_trans _ _ _ _ _ _ (constant_difference v (qmul u u))
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ (variance_literal z B h.andE₁.andE₂.andE₁.andE₁)))

theorem actual_original_Gamma_density_mean_variance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶
      crossEquivalent M constantF (GaussianGammaDensityMomentName.data (var 0) (var 1) (var 2) (var 3) one) (ofGaussian (var 0) (var 2)) ⋏
      crossEquivalent varianceF constantF (varianceData (var 0) (var 1) (var 2) (var 3)) (ofGaussian (var 0) (var 2))) :=
  closeUniv 4 (.impI (.andI (mean _ _ _ _ Prf.hyp0) (variance _ _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaDensityMeanVariance
