import IPRADerivations.Analysis.Barnes.FunctionalEquations.Hyperfactorial.Recurrence.GaussianBarnesCanonicalHyperfactorialPowerStep
import IPRADerivations.Analysis.Barnes.FunctionalEquations.GaussianBarnesCanonicalPoleFreeRecurrence
import IPRADerivations.Analysis.Barnes.CanonicalProducts.GaussianBarnesCanonicalProperness
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.GaussianLogGammaEulerPositiveAxis
import IPRADerivations.Analysis.Gamma.Names.PoleFree.GaussianGammaRadiusOverlap
import IPRADerivations.Analysis.Gamma.Names.Input.GaussianGammaInputProperness

/-! # The original Barnes denominator advances by the same Gamma multiplier -/

set_option autoImplicit false
set_option maxHeartbeats 1300000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHyperfactorialBarnesStep

open_ipra
open GaussianBarnesCanonicalHyperfactorial (center radius barnesData barnes_source barnes_regular specialLogData logarithm_source)
open GaussianBarnesCanonicalHyperfactorialExponentStep (centered_successor translated_center)
open GaussianBarnesCanonicalHyperfactorialPowerStep (gammaPowerF gammaPowerData gamma_power_regular logarithm_regular exponential_input)
open GaussianGammaEulerHeadLower (translated)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianGammaAdjacentCutoff (multiply_cross)
open ComplexLogarithmRemainder (oneCode scale)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "G" => GaussianBarnesCanonicalValue.nameF
local notation "L" => GaussianLogGammaEulerCofinal.nameF
local notation "ΓF" => GaussianGammaReciprocalInverse.gammaF
local notation "Γd" => GaussianGammaReciprocalInverse.gammaData
local notation "𝔞" t:max => Groth.ι (LeanProofs.IPRA.Q.mk Γ t)

abbrev denominatorF : PR 2 := multiplyF G gammaPowerF
def denominatorData (A B : PTm n) : PTm n := multiplyData G gammaPowerF (barnesData A B) (gammaPowerData A B)

private theorem real_margin (z A B : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hz : Γ ⊢[PRAAx] GaussianRootAlgebra.equal z (scale A oneCode)) :
    Γ ⊢[PRAAx] GaussianGammaRightHalfPlane.realMargin z B B := by
  apply zle_of_toZ (B*monus A one)
  have e := natEq (eq_add_of_le hA)
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,GaussianRootAlgebra.equal_re hz,
    GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one]
  ipra_simps
  linear_combination -𝔞 B*e

theorem gamma_source (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source (translated (center A B) B one) (radius A B+one) B one B := by
  let z := translated (center A B) B one
  let S := radius A B+one
  have ds : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z S B :=
    .andI (le_add_left one (radius A B)) (.andI hB
      (GaussianBarnesCanonicalShiftChart.translated_bound _ _ _ (barnes_source A B hB).andE₂))
  exact GaussianGammaRightHalfPlane.original_right_half_plane_source z S B B ds hB
    (real_margin z A B hA (translated_center A B))

theorem gamma_power_matches (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent gammaPowerF ΓF (gammaPowerData A B)
      (Γd (translated (center A B) B one) (radius A B+one) B B) := by
  let x := specialLogData A B
  let w := native A zero zero
  let z := translated (center A B) B one
  let R := GaussianLogGammaEulerResidualRadius.radius A zero
  let S := radius A B+one
  let V := GaussianNameBounds.U L x
  let W := GaussianLogGammaEulerExponentialLimit.disk A zero B zero
  have hl := logarithm_source A B hA hB
  have eq := GaussianLogGammaEulerPositiveAxis.native_axis_equal (Γ := Γ) A zero hl.andE₁.andE₂
  have move := GaussianRootAlgebra.equal_trans eq (GaussianRootAlgebra.equal_symm (translated_center A B))
  have src : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source w R B :=
    .andI (GaussianLogGammaEulerResidualRadius.radius_positive A zero B zero hl)
      (.andI hB (GaussianLogGammaEulerResidualRadius.source_of_right_half_plane A zero B zero hl).andE₂)
  have gsrc := GaussianGammaRightHalfPlane.original_right_half_plane_source w R B B src hB (real_margin w A B hA eq)
  have zsrc := GaussianGammaInputProperness.gamma_source_equal w z R B one B gsrc move
  have overlap := GaussianGammaRadiusOverlap.original_Gamma_overlap z R S B one B one B zsrc (gamma_source A B hA hB)
  have hx := exponential_input L x (logarithm_regular A B hA hB)
  have hw := GaussianExponentialRadiusIndependence.input_widen L V W x hx (le_add_right _ _)
  have exp := GaussianExponentialRadiusIndependence.same_input_cross L V W x hx hw
  have gamma := GaussianLogGammaEulerExponentialLimit.gamma_equivalent A zero B zero hl
  have proper := GaussianGammaInputProperness.original_Gamma_proper w z R B one B gsrc move
  exact cross_trans _ _ _ _ _ _ exp
    (cross_trans _ _ _ _ _ _ gamma (cross_trans _ _ _ _ _ _ proper overlap))

theorem denominator_step (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent G denominatorF (barnesData (A+B) B) (denominatorData A B) := by
  let z := center A B
  let w := translated z B one
  let R := radius A B
  let S := R+one
  have src := barnes_source A B hB
  have hg := gamma_source A B hA hB
  have eq := GaussianRootAlgebra.equal_trans (centered_successor (Γ := Γ) A B)
    (GaussianRootAlgebra.equal_symm (translated_center A B))
  have matchCenter := GaussianBarnesCanonicalProperness.proper (center (A+B) B) w (radius (A+B) B) S B B
    (barnes_source (A+B) B hB) (.andI hB hg.andE₁.andE₂.andE₂)
    (GaussianGammaFiniteValueProperness.fraction_equal _ _ _ hB eq)
  have step := GaussianBarnesCanonicalPoleFreeRecurrence.recurrence z R B one B src hg
  let x := barnesData A B
  let y := Γd w S B B
  let t := gammaPowerData A B
  have hr := barnes_regular A B hB
  have hGamma := GaussianGammaReciprocalInverse.gamma_regular w S B one B hg
  have hPower := gamma_power_regular A B hA hB
  have sameGamma := cross_symm gammaPowerF ΓF t y (gamma_power_matches A B hA hB)
  have right := multiply_cross G G ΓF gammaPowerF x x y t
    hr hr hGamma hPower (cross_refl _ _ hr) sameGamma
  exact cross_trans _ _ _ _ _ _ matchCenter (cross_trans _ _ _ _ _ _ step right)

theorem actual_Barnes_hyperfactorial_denominator_step_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (let A := var 0; let B := var 1
     le one A ⟶ le one B ⟶ crossEquivalent G denominatorF (barnesData (A+B) B) (denominatorData A B)) :=
  closeUniv 2 (.impI (.impI (denominator_step _ _ Prf.hyp0.wk Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHyperfactorialBarnesStep
