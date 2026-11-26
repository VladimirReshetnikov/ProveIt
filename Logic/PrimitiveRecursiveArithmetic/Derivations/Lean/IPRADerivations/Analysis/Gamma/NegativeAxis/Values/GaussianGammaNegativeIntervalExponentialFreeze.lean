import IPRADerivations.Analysis.Exponential.Estimates.GaussianRadiusExponentialLipschitzRate
import IPRADerivations.Analysis.Gamma.EulerProducts.Approximants.GaussianGammaFiniteApproximantName
import IPRADerivations.Analysis.Exponential.Names.GaussianExponentialRadiusIndependence
import IPRADerivations.Analysis.Names.Rates.Perturbations.GaussianNamedDifferenceRate
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateTransport
import IPRADerivations.Analysis.Polynomials.RootFinding.Reconstruction.GaussianReconstructionRoots

/-!
# Exponentiate a frozen logarithm with a uniform radius

A unit-leading rate bounds the second logarithm by the first logarithm's
radius plus three. The resulting exponential rate is independent of
the encoding and radius of the second logarithm.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalExponentialFreeze

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaFiniteApproximantName (exponentialInputData exponential_input)
open GaussianNameBounds (U sample_bound)
open GaussianNameRingLaws (three)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at denominator_positive)
open GaussianRadiusExponentialLipschitzRate (factor)
open GaussianRadiusExponentialName (input boundedSamples)
open GaussianRationalDistanceOrder (distance_radius_mono distance_symmetric)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "expF" => GaussianRadiusExponentialName.nameF
local notation "expData" => GaussianRadiusExponentialName.data

private theorem second_bound_at (F G : PR 2) (x y s t : PTm n) (hf : Γ ⊢[PRAAx] pointCN F x)
    (h : Γ ⊢[PRAAx] independentRate F G x y one (unit s)) :
    Γ ⊢[PRAAx] bounded (ap2 G t y) (U F x+three) one := by
  have un := unit_positive (Γ := Γ) s
  have hp := unit_positive (Γ := Γ) (zero : PTm n)
  have hq := unit_positive (Γ := Γ) t
  have hN := denominator_positive (unit s) zero t un
  have hrad : Γ ⊢[PRAAx] le (rateNumerator one (unit s) zero t*one) (three*rateDenominator (unit s) zero t) := by
    unfold rateNumerator rateDenominator three
    ipra_le 𝔞(unit zero)*𝔞(unit t)*sl un+
      𝔞(unit s)*𝔞(unit t)*sl hp+𝔞(unit s)*𝔞(unit zero)*sl hq
  have e := distance_radius_mono _ _ _ _ _ _ hN (le_refl one) hrad (rate_at F G x y one (unit s) zero t h)
  have r := GaussianReconstructionRoots.norm_from_distance (ap2 G t y) (ap2 F zero x) three one (U F x) one
    (le_refl one) (le_refl one) (distance_symmetric _ _ _ _ (le_refl one) e) (sample_bound F x zero hf)
  exact bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring) r

theorem second_input (F G : PR 2) (x y s : PTm n) (hf : Γ ⊢[PRAAx] pointCN F x) (hg : Γ ⊢[PRAAx] pointCN G y)
    (h : Γ ⊢[PRAAx] independentRate F G x y one (unit s)) :
    Γ ⊢[PRAAx] input G (U F x+three) y := by
  refine .andI hg (.allI ?_)
  let Δ := Γ.map Fm.shift
  let sh (v : PTm n) := Syn.shift v
  have left : Δ ⊢[PRAAx] pointCN F (sh x) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hf.shift
  have hr : Δ ⊢[PRAAx] independentRate F G (sh x) (sh y) one (unit (sh s)) := by
    simpa [Δ,sh,Fm.shift,Syn.shift,one] using h.shift
  simpa only [boundedSamples,sh,Syn.shift,PTm.subst_add,GaussianNameBounds.subst_U,three,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using second_bound_at F G (sh x) (sh y) (sh s) (var 0) left hr

theorem exponential_rate (F G : PR 2) (x y s : PTm n) (hf : Γ ⊢[PRAAx] pointCN F x)
    (hg : Γ ⊢[PRAAx] pointCN G y) (h : Γ ⊢[PRAAx] independentRate F G x y one (unit s)) :
    Γ ⊢[PRAAx] independentRate (expF F) (expF G) (exponentialInputData F x) (exponentialInputData G y)
      (factor (U F x+three)) (unit s) := by
  let R := U F x+three
  have hu := unit_positive (Γ := Γ) s
  have hF := exponential_input F x hf
  have hG := exponential_input G y hg
  have wF := GaussianExponentialRadiusIndependence.input_widen F (U F x) R x hF (le_add_right _ _)
  have wG := second_input F G x y s hf hg h
  have rate := GaussianRadiusExponentialLipschitzRate.independent_rate F G R x y one (unit s)
    (.andI hu (.andI wF (.andI wG h)))
  have moved := GaussianNamedRateTransport.transport (expF F) (expF G) (expF F) (expF G)
    (expData R x) (expData R y) (exponentialInputData F x) (exponentialInputData G y) (factor R*one) (unit s) hu
    rate (GaussianExponentialRadiusIndependence.same_input_cross F (U F x) R x hF wF)
    (GaussianExponentialRadiusIndependence.same_input_cross G (U G y) R y hG wG)
  exact GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _
    (by ipra_ring) (.eqRefl _) moved

theorem actual_uniform_exponential_freeze_closed (F G : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      ((pointCN F (var 0) ⋏ pointCN G (var 1)) ⟶
        independentRate F G (var 0) (var 1) one (unit (var 2)) ⟶
        independentRate (expF F) (expF G) (exponentialInputData F (var 0)) (exponentialInputData G (var 1))
          (factor (U F (var 0)+three)) (unit (var 2))) :=
  closeUniv 3 (.impI (.impI (exponential_rate F G _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalExponentialFreeze
