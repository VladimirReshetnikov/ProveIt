import IPRADerivations.Analysis.Barnes.FunctionalEquations.Hyperfactorial.GaussianBarnesCanonicalHyperfactorialExponentStep
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalProperness
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.GaussianLogGammaEulerPositiveAxis
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.GaussianLogGammaEulerRepresentation

/-! # Positive rational presentation independence of the original hyperfactorial -/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHyperfactorialProperness

open_ipra
open GaussianBarnesCanonicalHyperfactorial
  (center radius barnesData height barnes_source barnes_regular barnes_apart specialLogData logarithm_source
    exponentF exponentData powerF powerData power_input power_regular inverseF inverseData inverse_regular nameF data)
open GaussianBarnesCanonicalHyperfactorialExponentStep (point point_from_center)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical)
open GaussianRationalMetric (qsub)
open GaussianRationalSyntheticDivision (qone qsub_congr qadd_sub_cancel)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameEquivalence (crossEquivalent cross_to_diagonal)
open GaussianGammaAdjacentCutoff (multiply_cross)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "L" => GaussianLogGammaEulerCofinal.nameF
local notation "G" => GaussianBarnesCanonicalValue.nameF

theorem point_is_logarithm_argument (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] GaussianLogGammaEulerHead.argument A zero B zero ≐ point A B :=
  GaussianGammaFiniteValueProperness.fraction_equal _ _ _ hB
    (GaussianLogGammaEulerPositiveAxis.native_axis_equal A zero (.orI₁ (.eqRefl _)))

theorem center_fraction (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qsub (point A B) qone ≐ ofGaussian (center A B) B := by
  let c := ofGaussian (center A B) B
  have sum := (GaussianReciprocalHorner.qadd_commutative (Γ := Γ) qone c).eqTrans (point_from_center A B hB)
  exact (qsub_congr sum.eqSymm (.eqRefl qone)).eqTrans
    (qadd_sub_cancel qone c (ofGaussian_canonical _ _ hB))

theorem proper (A B a b : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (he : Γ ⊢[PRAAx] point A B ≐ point a b) :
    Γ ⊢[PRAAx] crossEquivalent nameF nameF (data A B) (data a b) := by
  have argEq := (point_is_logarithm_argument A B hB).eqTrans (he.eqTrans (point_is_logarithm_argument a b hb).eqSymm)
  have centerEq := (center_fraction A B hB).eqSymm.eqTrans
    ((qsub_congr he (.eqRefl _)).eqTrans (center_fraction a b hb))
  have logsrc := logarithm_source A B hA hB
  have logsrc' := logarithm_source a b ha hb
  have logEq := GaussianLogGammaEulerRepresentation.canonical_cross A zero B zero a zero b zero logsrc logsrc' argEq
  let c := ofGaussian (center A B) B
  let c' := ofGaussian (center a b) b
  have expEq := multiply_cross constantF constantF L L c c' (specialLogData A B) (specialLogData a b)
    (constant_regular c) (constant_regular c')
    (GaussianLogGammaEulerCofinal.canonical_regular A zero B zero logsrc)
    (GaussianLogGammaEulerCofinal.canonical_regular a zero b zero logsrc')
    (GaussianSignedNameExponentialOrder.constant_equal_cross _ _ centerEq) logEq
  have numEq := GaussianExponentialRadiusIndependence.independent_radii_proper exponentF exponentF _ _ _ _
    (power_input A B hA hB) (power_input a b ha hb) expEq
  have barnesEq := GaussianBarnesCanonicalProperness.proper (center A B) (center a b) (radius A B) (radius a b) B b
    (barnes_source A B hB) (barnes_source a b hb) centerEq
  have invEq := GaussianNameReciprocal.names_equivalent G G (height A B) (height a b) (barnesData A B) (barnesData a b)
    (barnes_regular A B hB) (barnes_regular a b hb) (barnes_apart A B hA hB) (barnes_apart a b ha hb)
    (cross_to_diagonal _ _ _ _ barnesEq)
  exact multiply_cross powerF powerF inverseF inverseF (powerData A B) (powerData a b) (inverseData A B) (inverseData a b)
    (power_regular A B hA hB) (power_regular a b ha hb) (inverse_regular A B hA hB) (inverse_regular a b ha hb)
    numEq invEq

theorem actual_original_Barnes_hyperfactorial_rational_proper_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (let A := var 0; let B := var 1; let a := var 2; let b := var 3
     (le one A ⋏ (le one B ⋏ (le one a ⋏ (le one b ⋏ point A B ≐ point a b)))) ⟶
       crossEquivalent nameF nameF (data A B) (data a b)) :=
  closeUniv 4 (.impI (proper _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHyperfactorialProperness
