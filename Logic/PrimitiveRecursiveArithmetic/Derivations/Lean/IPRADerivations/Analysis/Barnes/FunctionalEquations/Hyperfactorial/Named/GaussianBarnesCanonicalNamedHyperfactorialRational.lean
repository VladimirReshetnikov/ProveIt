import IPRADerivations.Analysis.Barnes.FunctionalEquations.Hyperfactorial.Named.GaussianBarnesCanonicalNamedHyperfactorial
import IPRADerivations.Analysis.Barnes.FunctionalEquations.Hyperfactorial.GaussianBarnesCanonicalHyperfactorial
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.RationalCharts.GaussianLogGammaEulerChartAgreement
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.NamedValues.GaussianLogGammaEulerPositiveAxis
import IPRADerivations.Analysis.Names.RightHalfPlane.GaussianNamedRightHalfPlaneConstant
import IPRADerivations.Analysis.Names.Rates.Order.GaussianNamedApartnessTransport

/-!
# Agreement of the named and positive rational Barnes hyperfactorials

The fixed rational name reads the original cofinal log-Gamma chart.
The actual shifted Barnes name agrees with the original positive
rational denominator. Transfer apartness and compare their actual
exponential and reciprocal names.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedHyperfactorialRational

open_ipra
open ComplexLogarithmRemainder (normSq_neg normSq_one oneCode scale)
open GaussianBarnesCanonicalOrdinaryUpperGrowth (minusOne valueData)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerNamed (rationalMap rationalData rational_data_at)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent cross_at cross_symm cross_to_diagonal cross_trans)
open GaussianNamedRightHalfPlaneSigned (realNumerator imagNumerator denominator sign point_eq_raw)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner
  (canonical_unique ofGaussian ofGaussian_canonical ofGaussian_represents positive_product qadd qadd_canonical
    qadd_represents represents_congr represents_rescale)
open GaussianRationalMetric (distanceBounded)
open GaussianRootAlgebra (equal equal_of_values re_neg im_neg re_scale im_scale)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "G" => GaussianBarnesCanonicalOrdinaryUpperGrowth.nameF
local notation "L" => GaussianLogGammaEulerNamed.nameF
local notation "F" => GaussianLogGammaEulerCofinal.nameF
local notation "ld" => GaussianLogGammaEulerNamed.data
local notation "Ls" => GaussianLogGammaEulerNamed.source

def positivePoint (A B : PTm n) : PTm n := argument A zero B zero
def radius (A B : PTm n) : PTm n := GaussianNamedRightHalfPlane.radius constantF (positivePoint A B)
def height (A B : PTm n) : PTm n := succ (GaussianBarnesCanonicalHyperfactorial.height A B)

@[simp] theorem subst_positivePoint {m : ℕ} (σ : Fin n → PTm m) (A B : PTm n) :
    Syn.subst σ (positivePoint A B) = positivePoint (Syn.subst σ A) (Syn.subst σ B) := by simp [positivePoint]

@[simp] theorem subst_radius {m : ℕ} (σ : Fin n → PTm m) (A B : PTm n) :
    Syn.subst σ (radius A B) = radius (Syn.subst σ A) (Syn.subst σ B) := by simp [radius]

theorem log_source (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] Ls constantF (positivePoint A B) B (radius A B) :=
  GaussianNamedRightHalfPlaneConstant.signed_rational_source A zero B zero (GaussianBarnesCanonicalHyperfactorial.logarithm_source A B hA hB)

private theorem log_observations (p q A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 (L constantF) p (ld (positivePoint A B) B (radius A B))) (ap2 F q (GaussianBarnesCanonicalHyperfactorial.specialLogData A B))
      (unit p+unit q) (unit p*unit q) := by
  let x := positivePoint A B
  let R := radius A B
  let k := GaussianNamedRightHalfPlaneLift.clock rationalMap p B R
  have h := GaussianBarnesCanonicalHyperfactorial.logarithm_source A B hA hB
  have cert := GaussianNamedRightHalfPlaneConstant.signed_rational_certificate A zero B zero h
  have canon : Γ ⊢[PRAAx] GaussianRationalHorner.canonical x :=
    ofGaussian_canonical (native A zero zero) B hB
  have link := point_eq_raw x cert.andE₁.andE₁.andE₁.andE₁ canon
  have chart := GaussianLogGammaEulerChartAgreement.canonical_agreement (realNumerator x) (imagNumerator x)
    (denominator x) (sign x) A zero B zero cert.andE₁.andE₁ h link
  have obs := cross_at F F (GaussianLogGammaEulerNamed.pointData x) (GaussianBarnesCanonicalHyperfactorial.specialLogData A B) (succ p) q chart
  have grow := unit_monotone (Γ := Γ) (le_succ_self p)
  have fit : Γ ⊢[PRAAx] le ((unit (succ p)+unit q)*(unit p*unit q)) ((unit p+unit q)*(unit (succ p)*unit q)) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add₂ (le_refl (unit p*unit (succ p)*unit q)) (mul_le_mul_right (unit q*unit q) grow))
  have near := distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (unit_positive (succ p)) (unit_positive q))
    (positive_product _ _ (unit_positive p) (unit_positive q)) fit obs
  have read := (congrAp1 rationalData (constant_at (Γ := Γ) k x)).eqTrans (rational_data_at x)
  have sample := (GaussianNamedRightHalfPlaneLift.sample_at rationalMap constantF p x B R).eqTrans
    (congrAp2 F (.eqRefl (succ p)) read)
  exact distance_congr sample.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) near

theorem log_cross (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent (L constantF) F (ld (positivePoint A B) B (radius A B)) (GaussianBarnesCanonicalHyperfactorial.specialLogData A B) := by
  refine .allI (.allI ?_)
  let sh (u : PTm n) := Syn.shift (Syn.shift u)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have a : Δ ⊢[PRAAx] le one (sh A) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hA.shift.shift
  have b : Δ ⊢[PRAAx] le one (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hB.shift.shift
  simpa only [crossEquivalent,GaussianNamedRightHalfPlaneLift.subst_data,subst_positivePoint,
    subst_radius,GaussianBarnesCanonicalHyperfactorial.subst_specialLogData,Syn.shift,sh,Δ] using log_observations (var 1) (var 0) (sh A) (sh B) a b

theorem shift_fraction (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qadd (positivePoint A B) minusOne ≐ ofGaussian (GaussianBarnesCanonicalHyperfactorial.center A B) B := by
  let x := positivePoint A B
  let u := scale A oneCode
  let minus : PTm n := ComplexLogarithmRemainder.neg oneCode
  let v := ComplexLogarithmRemainder.neg (scale B oneCode)
  let w := GaussianBarnesCanonicalHyperfactorial.center A B
  have hx := represents_congr (.eqRefl x) (GaussianLogGammaEulerPositiveAxis.native_axis_equal A zero (.orI₁ (.eqRefl _)))
    (.eqRefl B) (ofGaussian_represents (native A zero zero) B hB)
  have ev : Γ ⊢[PRAAx] equal (scale B minus) v := by
    apply equal_of_values <;> simp only [minus,v,re_scale,re_neg,im_scale,im_neg] <;> ring
  have hv := represents_congr (.eqRefl minusOne) ev (one_mul B)
    (represents_rescale minusOne minus one B (ofGaussian_represents minus one (le_refl one)))
  exact canonical_unique _ _ w B (qadd_canonical x minusOne) (ofGaussian_canonical w B hB) hB
    (qadd_represents x minusOne u v B hB hx hv) (ofGaussian_represents w B hB)

private theorem shift_cross (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent (addF constantF constantF) constantF (addData (positivePoint A B) minusOne)
      (ofGaussian (GaussianBarnesCanonicalHyperfactorial.center A B) B) :=
  GaussianNamedGammaHalfShift.constant_sum (positivePoint A B) minusOne _ (shift_fraction A B hB)

private theorem minus_source : Γ ⊢[PRAAx] GaussianBarnesCanonicalNamedDemand.source constantF minusOne one := by
  have h : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (ComplexLogarithmRemainder.neg oneCode) (one*one) :=
    le_congr ((normSq_neg oneCode).eqTrans normSq_one).eqSymm (by ipra_ring) (le_refl one)
  exact GaussianBarnesCanonicalNamed.constant_source _ _ _ (.andI (le_refl one) h)

theorem barnes_cross (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent (G constantF) GaussianBarnesCanonicalValue.nameF
      (valueData (positivePoint A B) (radius A B)) (GaussianBarnesCanonicalHyperfactorial.barnesData A B) := by
  let x := positivePoint A B
  let R := radius A B
  let y := ofGaussian (GaussianBarnesCanonicalHyperfactorial.center A B) B
  let S := GaussianBarnesCanonicalHyperfactorial.radius A B
  have hz := GaussianBarnesCanonicalHyperfactorial.barnes_source A B hB
  have hs := GaussianBarnesCanonicalNamedHyperfactorial.barnes_source constantF x B R (log_source A B hA hB)
  have shift := GaussianBarnesCanonicalNamedIncrementEndpoints.shifted_source constantF constantF x minusOne R hs minus_source
  have ready := GaussianBarnesCanonicalNamed.constant_source (GaussianBarnesCanonicalHyperfactorial.center A B) S B hz
  have he := GaussianBarnesCanonicalNamedFrozen.proper (addF constantF constantF) constantF (addData x minusOne)
    y (R+one) S shift ready (shift_cross A B hB)
  exact cross_trans _ _ _ _ _ _ he (GaussianBarnesCanonicalNamed.constant_cross (GaussianBarnesCanonicalHyperfactorial.center A B) S B hz)

theorem source (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] GaussianBarnesCanonicalNamedHyperfactorial.source constantF (positivePoint A B) B (radius A B) (height A B) := by
  refine .andI (log_source A B hA hB) ?_
  exact GaussianNamedApartnessTransport.transport GaussianBarnesCanonicalValue.nameF (G constantF)
    (GaussianBarnesCanonicalHyperfactorial.height A B) (GaussianBarnesCanonicalHyperfactorial.barnesData A B) (valueData (positivePoint A B) (radius A B))
    (GaussianBarnesCanonicalHyperfactorial.barnes_apart A B hA hB) (cross_symm _ _ _ _ (barnes_cross A B hA hB))

theorem power_cross (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianBarnesCanonicalNamedHyperfactorial.powerF constantF) GaussianBarnesCanonicalHyperfactorial.powerF
      (GaussianBarnesCanonicalNamedHyperfactorial.powerData constantF (positivePoint A B) B (radius A B)) (GaussianBarnesCanonicalHyperfactorial.powerData A B) := by
  let x := positivePoint A B
  let R := radius A B
  let h := log_source A B hA hB
  have input := GaussianGammaAdjacentCutoff.multiply_cross (addF constantF constantF) constantF (L constantF) F
    (addData x minusOne) (ofGaussian (GaussianBarnesCanonicalHyperfactorial.center A B) B) (ld x B R) (GaussianBarnesCanonicalHyperfactorial.specialLogData A B)
    (add_fast _ _ _ _ (constant_regular x) (constant_regular minusOne)) (constant_regular _)
    (GaussianLogGammaEulerNamed.name_regular constantF x B R h)
    (GaussianLogGammaEulerCofinal.canonical_regular A zero B zero (GaussianBarnesCanonicalHyperfactorial.logarithm_source A B hA hB))
    (shift_cross A B hB) (log_cross A B hA hB)
  exact GaussianExponentialRadiusIndependence.independent_radii_proper (GaussianBarnesCanonicalNamedHyperfactorial.exponentF constantF) GaussianBarnesCanonicalHyperfactorial.exponentF
    (GaussianBarnesCanonicalNamedHyperfactorial.powerRadius constantF x B R)
    (GaussianBarnesCanonicalHyperfactorial.powerRadius A B)
    (GaussianBarnesCanonicalNamedHyperfactorial.exponentData constantF x B R)
    (GaussianBarnesCanonicalHyperfactorial.exponentData A B)
    (GaussianBarnesCanonicalNamedHyperfactorial.power_input constantF x B R h) (GaussianBarnesCanonicalHyperfactorial.power_input A B hA hB) input

theorem agreement (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianBarnesCanonicalNamedHyperfactorial.nameF constantF) GaussianBarnesCanonicalHyperfactorial.nameF
      (GaussianBarnesCanonicalNamedHyperfactorial.data constantF (positivePoint A B) B (radius A B) (height A B)) (GaussianBarnesCanonicalHyperfactorial.data A B) := by
  let x := positivePoint A B
  let R := radius A B
  let h := height A B
  have hs := source A B hA hB
  have same := barnes_cross A B hA hB
  have hinv := GaussianNameReciprocal.names_equivalent (G constantF) GaussianBarnesCanonicalValue.nameF h (GaussianBarnesCanonicalHyperfactorial.height A B)
    (valueData x R) (GaussianBarnesCanonicalHyperfactorial.barnesData A B)
    (GaussianBarnesCanonicalNamedHyperfactorial.barnes_regular constantF x B R hs.andE₁)
    (GaussianBarnesCanonicalHyperfactorial.barnes_regular A B hB)
    hs.andE₂ (GaussianBarnesCanonicalHyperfactorial.barnes_apart A B hA hB) (cross_to_diagonal _ _ _ _ same)
  exact GaussianGammaAdjacentCutoff.multiply_cross
    (GaussianBarnesCanonicalNamedHyperfactorial.powerF constantF) GaussianBarnesCanonicalHyperfactorial.powerF
    (GaussianBarnesCanonicalNamedHyperfactorial.inverseF constantF) GaussianBarnesCanonicalHyperfactorial.inverseF
    (GaussianBarnesCanonicalNamedHyperfactorial.powerData constantF x B R) (GaussianBarnesCanonicalHyperfactorial.powerData A B)
    (GaussianBarnesCanonicalNamedHyperfactorial.inverseData x R h) (GaussianBarnesCanonicalHyperfactorial.inverseData A B)
    (GaussianBarnesCanonicalNamedHyperfactorial.power_regular constantF x B R hs.andE₁) (GaussianBarnesCanonicalHyperfactorial.power_regular A B hA hB)
    (GaussianBarnesCanonicalNamedHyperfactorial.inverse_regular constantF x B R h hs) (GaussianBarnesCanonicalHyperfactorial.inverse_regular A B hA hB)
    (power_cross A B hA hB) hinv

theorem actual_named_Barnes_hyperfactorial_positive_rational_agreement_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (let A := var 0
       let B := var 1
       le one A ⟶ le one B ⟶
         crossEquivalent (GaussianBarnesCanonicalNamedHyperfactorial.nameF constantF) GaussianBarnesCanonicalHyperfactorial.nameF
           (GaussianBarnesCanonicalNamedHyperfactorial.data constantF (positivePoint A B) B (radius A B) (height A B)) (GaussianBarnesCanonicalHyperfactorial.data A B)) :=
  closeUniv 2 (.impI (.impI (agreement _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedHyperfactorialRational
