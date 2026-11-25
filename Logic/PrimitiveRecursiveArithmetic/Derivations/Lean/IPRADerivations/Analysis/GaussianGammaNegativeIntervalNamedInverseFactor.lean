import IPRADerivations.Analysis.GaussianGammaNegativeIntervalInverseRationalEnvelope
import IPRADerivations.Analysis.GaussianNamedUnitIntervalRationalLift
import IPRADerivations.Analysis.GaussianGammaNegativeIntervalNamedInput

/-!
# The finite inverse shift factor on named negative intervals

The primitive-recursive evaluator freezes the offset, reads the
original inverse finite shift product, and pays its uniform
rational Lipschitz constant in the sample clock.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedInverseFactor

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF)
open GaussianGammaNegativeIntervalInverseRecurrence (inverse subst_inverse)
open GaussianGammaNegativeIntervalNamedInput (sampleNumerator sampleDenominator)
open GaussianGammaNegativeProductDerivativeInverseRate (inverseGapCost)
open GaussianNamedEulerUnitTime (source)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedUnitIntervalRationalLift (RationalMap)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rationalF : PR 3 := PTm.toPR (inverse (var 0) (var 1) (var 2) : PTm 3)

theorem rational_at (a b N : PTm n) : Γ ⊢[PRAAx] ap3 rationalF a b N ≐ inverse a b N := by
  simpa [rationalF,ap3] using toPR_eq (Γ := Γ) (inverse (var 0) (var 1) (var 2) : PTm 3) ![a,b,N]

def rationalMap : RationalMap where
  evaluator := rationalF
  gain E N := inverseGapCost (succ N) (E*E)
  subst_gain σ E N := by simp
  variation a b c d E N A D ha hc hD h := by
    have rev := distance_symmetric _ _ _ _ hD h
    have result := (GaussianGammaNegativeIntervalInverseRationalEnvelope.window_envelope a b c d E N A D ha hc hD rev).andE₁
    exact distance_congr (rational_at a b N).eqSymm (rational_at c d N).eqSymm (.eqRefl _) (.eqRefl _)
      (distance_symmetric _ _ _ _ hD result)

abbrev nameF (f : PR 2) : PR 2 := GaussianNamedUnitIntervalRationalLift.nameF rationalMap f
abbrev data (x E N : PTm n) : PTm n := GaussianNamedUnitIntervalRationalLift.data x E N
abbrev clock (p E N : PTm n) : PTm n := GaussianNamedUnitIntervalRationalLift.clock rationalMap p E N

theorem name_regular (f : PR 2) (x E N : PTm n) (h : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data x E N) :=
  GaussianNamedUnitIntervalRationalLift.name_regular rationalMap f x E N h

theorem original_frozen_rate (f : PR 2) (s k x E N : PTm n) (h : Γ ⊢[PRAAx] source f x E)
    (hk : Γ ⊢[PRAAx] le (clock s E N) k) :
    Γ ⊢[PRAAx] independentRate (nameF f) constantF (data x E N)
      (inverse (sampleNumerator f k x) (sampleDenominator f k x) N) one (unit s) := by
  let z := GaussianNamedUnitIntervalRationalLift.frozen rationalMap f k x N
  let w := inverse (sampleNumerator f k x) (sampleDenominator f k x) N
  have eq : Γ ⊢[PRAAx] z ≐ w := rational_at _ _ _
  exact GaussianNamedRateTransport.transport (nameF f) constantF (nameF f) constantF (data x E N) z
    (data x E N) w one (unit s) (GaussianCoefficientNameBounds.unit_positive s)
    (GaussianNamedUnitIntervalRationalLift.original_frozen_rate rationalMap f s k x E N h hk)
    (GaussianNameEquivalence.cross_refl _ _ (name_regular f x E N h))
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ eq.eqSymm)

theorem actual_named_negative_Gamma_inverse_factor_frozen_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source f (var 0) (var 1) ⟶ le (clock (var 3) (var 1) (var 2)) (var 4) ⟶
        independentRate (nameF f) constantF (data (var 0) (var 1) (var 2))
          (inverse (sampleNumerator f (var 4) (var 0)) (sampleDenominator f (var 4) (var 0)) (var 2))
          one (unit (var 3))) :=
  closeUniv 5 (.impI (.impI (original_frozen_rate f _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedInverseFactor
