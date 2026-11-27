import IPRADerivations.Analysis.Gamma.NegativeAxis.Derivatives.CoefficientVariation.GaussianGammaNegativeIntervalCorrectionVariation
import IPRADerivations.Analysis.Names.Approximation.GaussianNamedUnitIntervalRationalLift
import IPRADerivations.Analysis.Gamma.NegativeAxis.Input.GaussianGammaNegativeIntervalNamedInput

/-!
# The inverse shift derivative on named negative intervals

The evaluator reads the actual derivative coefficient at a later
rational observation. Its uniform rational Lipschitz bound gives a
regular name and a rate against every sufficiently late observation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedCorrectionFactor

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF)
open GaussianGammaNegativeIntervalCorrectionVariation (gain subst_gain rational_variation)
open GaussianGammaNegativeIntervalInverseRecurrence (correctionFactor)
open GaussianGammaNegativeIntervalNamedInput (sampleNumerator sampleDenominator)
open GaussianNameEquivalence (cross_refl)
open GaussianNamedEulerUnitTime (source)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedUnitIntervalRationalLift (RationalMap)
open GaussianRationalDistanceOrder (distance_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rationalF : PR 3 := PTm.toPR (correctionFactor (var 0) (var 1) (var 2) : PTm 3)

theorem rational_at (a b N : PTm n) : Γ ⊢[PRAAx] ap3 rationalF a b N ≐ correctionFactor a b N := by
  simpa [rationalF, ap3] using toPR_eq (Γ := Γ) (correctionFactor (var 0) (var 1) (var 2) : PTm 3) ![a,b,N]

def rationalMap : RationalMap where
  evaluator := rationalF
  gain := gain
  subst_gain := subst_gain
  variation a b c d E N A D ha hc hD h :=
    distance_congr (rational_at a b N).eqSymm (rational_at c d N).eqSymm (.eqRefl _) (.eqRefl _)
      (rational_variation a b c d E N A D ha hc hD h)

abbrev nameF (f : PR 2) : PR 2 := GaussianNamedUnitIntervalRationalLift.nameF rationalMap f
abbrev data (x E N : PTm n) : PTm n := GaussianNamedUnitIntervalRationalLift.data x E N
abbrev clock (p E N : PTm n) : PTm n := GaussianNamedUnitIntervalRationalLift.clock rationalMap p E N

theorem name_regular (f : PR 2) (x E N : PTm n) (h : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data x E N) :=
  GaussianNamedUnitIntervalRationalLift.name_regular rationalMap f x E N h

theorem original_frozen_rate (f : PR 2) (s k x E N : PTm n) (h : Γ ⊢[PRAAx] source f x E)
    (hk : Γ ⊢[PRAAx] le (clock s E N) k) :
    Γ ⊢[PRAAx] independentRate (nameF f) constantF (data x E N)
      (correctionFactor (sampleNumerator f k x) (sampleDenominator f k x) N) one (unit s) := by
  let z := GaussianNamedUnitIntervalRationalLift.frozen rationalMap f k x N
  let w := correctionFactor (sampleNumerator f k x) (sampleDenominator f k x) N
  have eq : Γ ⊢[PRAAx] z ≐ w := rational_at _ _ _
  exact GaussianNamedRateTransport.transport (nameF f) constantF (nameF f) constantF (data x E N) z
    (data x E N) w one (unit s) (unit_positive s)
    (GaussianNamedUnitIntervalRationalLift.original_frozen_rate rationalMap f s k x E N h hk)
    (cross_refl _ _ (name_regular f x E N h))
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ eq.eqSymm)

theorem actual_named_negative_Gamma_correction_factor_frozen_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source f (var 0) (var 1) ⟶ le (clock (var 3) (var 1) (var 2)) (var 4) ⟶
        independentRate (nameF f) constantF (data (var 0) (var 1) (var 2))
          (correctionFactor (sampleNumerator f (var 4) (var 0)) (sampleDenominator f (var 4) (var 0)) (var 2))
          one (unit (var 3))) :=
  closeUniv 5 (.impI (.impI (original_frozen_rate f _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedCorrectionFactor
