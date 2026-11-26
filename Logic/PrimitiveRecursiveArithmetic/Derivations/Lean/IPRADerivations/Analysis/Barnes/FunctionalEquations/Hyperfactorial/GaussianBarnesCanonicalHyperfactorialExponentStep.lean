import IPRADerivations.Analysis.Barnes.FunctionalEquations.Hyperfactorial.GaussianBarnesCanonicalHyperfactorial
import IPRADerivations.Analysis.Barnes.FunctionalEquations.UnitShift.GaussianBarnesCanonicalShiftChart
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Recurrence.GaussianLogGammaEulerRecurrence
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.GaussianNamedGammaHalfShift

/-! # The unit increment of the exact hyperfactorial numerator exponent -/

set_option autoImplicit false
set_option maxHeartbeats 1300000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHyperfactorialExponentStep

open_ipra
open GaussianBarnesCanonicalHyperfactorial
  (center specialLogData exponentF exponentData exponent_regular logarithm_source)
open GaussianGammaCanonicalExponent (constantF constant_regular constant_at)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (add_associative add_commutative add_negative zeroF zero_fast zero_at
  multiply_one_left oneF one_at one_fast negativeF negativeData negative_fast distributive right_distributive)
open GaussianNamedGammaHalfShift (add_cross constant_sum)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalHorner (ofGaussian qadd)
open GaussianRationalSyntheticDivision (qone)
open GaussianGammaEulerHeadLower (translated)
open ComplexLogarithmRemainder (scale oneCode)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "L" => GaussianLogGammaEulerCofinal.nameF
local notation "T" => GaussianRightHalfPlaneLogarithm.nameF
local notation "Df" => GaussianNamedDifference.nameF
local notation "Dd" => GaussianNamedDifference.data

def point (A B : PTm n) : PTm n := ofGaussian (scale A oneCode) B
def logarithmData (A B : PTm n) : PTm n := GaussianRightHalfPlaneLogarithm.data A zero B zero
abbrev stepExponentF : PR 2 := multiplyF constantF T
def stepExponentData (A B : PTm n) : PTm n := multiplyData constantF T (point A B) (logarithmData A B)
abbrev incrementF : PR 2 := addF L stepExponentF
def incrementData (A B : PTm n) : PTm n := addData (specialLogData A B) (stepExponentData A B)
abbrev totalF : PR 2 := addF exponentF incrementF
def totalData (A B : PTm n) : PTm n := addData (exponentData A B) (incrementData A B)

theorem centered_successor (A B : PTm n) : Γ ⊢[PRAAx]
    GaussianRootAlgebra.equal (center (A+B) B) (scale A oneCode) := by
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [center,GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,GaussianRootAlgebra.re_scale,
      GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;>
    ipra_simps <;> ring

theorem translated_center (A B : PTm n) : Γ ⊢[PRAAx]
    GaussianRootAlgebra.equal (translated (center A B) B one) (scale A oneCode) := by
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [translated,center,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,
      GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,GaussianRootAlgebra.re_scale,
      GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;>
    ipra_simps <;> ring

theorem point_from_center (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qadd (ofGaussian (center A B) B) qone ≐ point A B :=
  (GaussianBarnesCanonicalShiftChart.translated_fraction (center A B) B hB).eqTrans
    (GaussianGammaFiniteValueProperness.fraction_equal _ _ _ hB (translated_center A B))

private theorem constant_one (x : PTm n) : Γ ⊢[PRAAx] crossEquivalent constantF oneF qone x := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (constant_regular _) (one_fast x)
  refine .allI ?_
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift,GaussianRationalSyntheticDivision.subst_qone] using
    (constant_at (var 0) qone).eqTrans (one_at (var 0) (Syn.shift x)).eqSymm

private theorem add_back (f g : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) :
    Γ ⊢[PRAAx] crossEquivalent (addF (Df f g) g) f (addData (Dd x y) y) x := by
  let neg := negativeF g
  let w := negativeData y
  have hr := negative_fast g y hg
  have hb := add_fast neg g w y hr hg
  have comm := add_commutative neg g w y hr hg
  have canc := cross_trans _ _ _ _ _ _ comm (add_negative g y hg)
  have zs : Γ ⊢[PRAAx] crossEquivalent zeroF zeroF y x := by
    apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (zero_fast y) (zero_fast x)
    refine .allI ?_
    simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift] using
      (zero_at (var 0) (Syn.shift y)).eqTrans (zero_at (var 0) (Syn.shift x)).eqSymm
  have zero := cross_trans _ _ _ _ _ _ canc zs
  have replace := add_cross f f (addF neg g) zeroF x x (addData w y) x
    hf hf hb (zero_fast x) (cross_refl _ _ hf) zero
  exact cross_trans _ _ _ _ _ _ (add_associative f neg g x w y hf hr hg)
    (cross_trans _ _ _ _ _ _ replace (GaussianNameRingLaws.add_zero f x hf))

theorem logarithm_sum (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent L (addF L T) (specialLogData (A+B) B)
      (addData (specialLogData A B) (logarithmData A B)) := by
  let x := specialLogData A B
  let y := specialLogData (A+B) B
  let t := logarithmData A B
  have h := logarithm_source A B hA hB
  have hs := logarithm_source (A+B) B (le_trans hA (le_add_right _ _)) hB
  have hx := GaussianLogGammaEulerCofinal.canonical_regular A zero B zero h
  have hy := GaussianLogGammaEulerCofinal.canonical_regular (A+B) zero B zero hs
  have ht := GaussianRightHalfPlaneLogarithm.regular A zero B zero h
  have dd := GaussianNamedDifference.name_regular L L y x hy hx
  have move := add_cross (Df L L) T L L (Dd y x) t x x dd ht hx hx
    (GaussianLogGammaEulerRecurrence.recurrence A zero B zero h) (cross_refl _ _ hx)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (add_back L L y x hy hx))
    (cross_trans _ _ _ _ _ _ move (add_commutative T L t x ht hx))

theorem step_exponent_regular (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] pointCN stepExponentF (stepExponentData A B) :=
  multiply_fast _ _ _ _ (constant_regular _)
    (GaussianRightHalfPlaneLogarithm.regular A zero B zero (logarithm_source A B hA hB))

private theorem weighted_log_split (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent exponentF (addF exponentF L)
      (multiplyData constantF L (point A B) (specialLogData A B))
      (addData (exponentData A B) (specialLogData A B)) := by
  let C := constantF
  let u := ofGaussian (center A B) B
  let w := point A B
  let x := specialLogData A B
  let e := exponentData A B
  have hx := GaussianLogGammaEulerCofinal.canonical_regular A zero B zero (logarithm_source A B hA hB)
  have hU := constant_regular (Γ := Γ) u
  have hOne := constant_regular (Γ := Γ) (qone : PTm n)
  have sum := constant_sum u qone w (point_from_center A B hB)
  have replace := multiply_cross C (addF C C) L L w (addData u qone) x x
    (constant_regular _) (add_fast C C _ _ hU hOne) hx hx (cross_symm _ _ _ _ sum) (cross_refl _ _ hx)
  have dist := right_distributive C C L u qone x hU hOne hx
  have step := multiply_cross C oneF L L (qone : PTm n) x x x
    hOne (one_fast x) hx hx (constant_one x) (cross_refl _ _ hx)
  have unit := cross_trans _ _ _ _ _ _ step (multiply_one_left L x hx)
  have sumStep := add_cross exponentF exponentF (multiplyF C L) L e e (multiplyData C L qone x) x
    (exponent_regular A B hA hB) (exponent_regular A B hA hB)
    (multiply_fast C L _ _ hOne hx) hx (cross_refl _ _ (exponent_regular A B hA hB)) unit
  exact cross_trans _ _ _ _ _ _ replace (cross_trans _ _ _ _ _ _ dist sumStep)

theorem exponent_step (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent exponentF totalF (exponentData (A+B) B) (totalData A B) := by
  let C := constantF
  let x := specialLogData A B
  let y := specialLogData (A+B) B
  let t := logarithmData A B
  let w := point A B
  let w' := ofGaussian (center (A+B) B) B
  have hx := GaussianLogGammaEulerCofinal.canonical_regular A zero B zero (logarithm_source A B hA hB)
  have hy := GaussianLogGammaEulerCofinal.canonical_regular (A+B) zero B zero
    (logarithm_source (A+B) B (le_trans hA (le_add_right _ _)) hB)
  have ht := GaussianRightHalfPlaneLogarithm.regular A zero B zero (logarithm_source A B hA hB)
  have hw := constant_regular (Γ := Γ) w
  have hc := GaussianGammaFiniteValueProperness.fraction_equal _ _ _ hB (centered_successor A B)
  have replace := multiply_cross C C L (addF L T) w' w y (addData x t)
    (constant_regular _) hw hy (add_fast _ _ _ _ hx ht)
    (GaussianSignedNameExponentialOrder.constant_equal_cross _ _ hc) (logarithm_sum A B hA hB)
  have expand := distributive C L T w x t hw hx ht
  have hstep := step_exponent_regular A B hA hB
  have he := exponent_regular A B hA hB
  have split := add_cross exponentF (addF exponentF L) stepExponentF stepExponentF
    (multiplyData C L w x) (addData (exponentData A B) x) (stepExponentData A B) (stepExponentData A B)
    (multiply_fast C L w x hw hx) (add_fast _ _ _ _ he hx) hstep hstep
    (weighted_log_split A B hA hB) (cross_refl _ _ hstep)
  have group := add_associative exponentF L stepExponentF (exponentData A B) x (stepExponentData A B) he hx hstep
  exact cross_trans _ _ _ _ _ _ replace
    (cross_trans _ _ _ _ _ _ expand (cross_trans _ _ _ _ _ _ split group))

theorem actual_Barnes_hyperfactorial_exponent_step_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (let A := var 0; let B := var 1
     le one A ⟶ le one B ⟶
       crossEquivalent exponentF totalF (exponentData (A+B) B) (totalData A B)) :=
  closeUniv 2 (.impI (.impI (exponent_step _ _ Prf.hyp0.wk Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHyperfactorialExponentStep
