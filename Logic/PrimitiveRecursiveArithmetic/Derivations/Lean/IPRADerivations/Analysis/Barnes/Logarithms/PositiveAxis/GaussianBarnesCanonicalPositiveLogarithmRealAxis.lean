import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.GaussianBarnesCanonicalPositiveLogarithm
import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.GaussianBarnesCanonicalPositiveHeadRealAxis
import IPRADerivations.Analysis.Barnes.Logarithms.GaussianBarnesCanonicalLogarithmRealTail
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalProperness
import IPRADerivations.Analysis.Logarithm.PositiveAxis.GaussianNamedPositiveLogarithmScale

/-!
# The real positive-axis logarithm of the original Barnes evaluator

All original exponent components are real at their actual clocks. Real
exponential injectivity then identifies the logarithm across independently
chosen certified radii and equal rational center presentations.
-/

set_option autoImplicit false
set_option maxHeartbeats 550000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveLogarithmRealAxis

open_ipra
open ComplexLogarithmRemainder (im eval_im_code)
open GaussianBarnesCanonicalPositiveLogarithm (source nameF data expData default_source regular exponential_value)
open GaussianBarnesCanonicalThirdLogarithmRows (center)
open GaussianGammaFiniteApproximantName (exponential_input exponentialInputData)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm)
open GaussianRealNameExponentialInjectivity (axisSamples independent_radii_injective)
open GaussianRationalHorner (ofGaussian)
open GaussianSignedNameExponentialOrder (realSamples)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "V" => GaussianBarnesCanonicalValue.nameF
local notation "vd" => GaussianBarnesCanonicalValue.data

theorem real_axis (f : PR 2) (x : PTm n) (h : Γ ⊢[PRAAx] realSamples f x) : Γ ⊢[PRAAx] axisSamples f x :=
  .allI ((GaussianSignedNameExponentialOrder.real_sample_at f (Syn.shift x) (var 0)
    (by simpa only [Fm.shift,Syn.shift,GaussianSignedNameExponentialOrder.subst_realSamples] using h.shift)).andE₂)

theorem center_axis (a b : PTm n) : Γ ⊢[PRAAx] ZT.eq (im (center a b)) (ZT.ofNat zero) :=
  ZT.derive (by simp only [center,eval_im_code])

theorem samples_axis (a b R : PTm n) (hs : Γ ⊢[PRAAx] source a b R) :
    Γ ⊢[PRAAx] axisSamples nameF (data a b R) := by
  let z := center a b
  let P := GaussianBarnesCanonicalSingleExponential.prefixF
  let L := GaussianBarnesCanonicalLogCofinal.nameF
  let x := GaussianBarnesCanonicalSingleExponential.prefixData z R b
  let y := GaussianBarnesCanonicalLogCofinal.data z R b
  have prefixReal := GaussianBarnesCanonicalLogarithmRealPrefix.prefix_real z R b hs.andE₂.andE₁ (center_axis a b)
  have tail := GaussianBarnesCanonicalLogarithmRealTail.cofinal_real z R b (center_axis (Γ := Γ) a b)
  have exponent := real_axis _ _ (GaussianStirlingNames.add_real P L x y prefixReal tail)
  exact GaussianNamedPositiveLogarithmScale.sum_axis _ _ _ _
    (GaussianBarnesCanonicalPositiveHeadRealAxis.real_samples a b _) exponent

theorem proper (a b c d R S : PTm n) (ha : Γ ⊢[PRAAx] source a b R) (hc : Γ ⊢[PRAAx] source c d S)
    (he : Γ ⊢[PRAAx] ofGaussian (center a b) b ≐ ofGaussian (center c d) d) : Γ ⊢[PRAAx]
    crossEquivalent nameF nameF (data a b R) (data c d S) := by
  have expEq := GaussianBarnesCanonicalProperness.proper (center a b) (center c d) R S b d ha.andE₂ hc.andE₂ he
  exact independent_radii_injective nameF nameF (U nameF (data a b R)) (U nameF (data c d S)) _ _
    (exponential_input _ _ (regular a b R ha)) (exponential_input _ _ (regular c d S hc))
    (samples_axis a b R ha) (samples_axis c d S hc)
    (cross_trans (E nameF) V (E nameF) _ _ _ (exponential_value a b R ha)
      (cross_trans _ _ _ _ _ _ expEq (cross_symm _ _ _ _ (exponential_value c d S hc))))

theorem actual_Barnes_positive_real_logarithm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (let a := var 0
     let b := var 1
     (le one a ⋏ le one b) ⟶ axisSamples nameF (data a b (a+b)) ⋏
       crossEquivalent (E nameF) V (expData a b (a+b)) (vd (center a b) (a+b) b)) := by
  refine closeUniv 2 (.impI ?_)
  have hs : [le one (var 0 : PTm 2) ⋏ le one (var 1)] ⊢[PRAAx] source (var 0) (var 1) (var 0+var 1) :=
    default_source _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂
  exact .andI (samples_axis _ _ _ hs) (exponential_value _ _ _ hs)

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveLogarithmRealAxis
