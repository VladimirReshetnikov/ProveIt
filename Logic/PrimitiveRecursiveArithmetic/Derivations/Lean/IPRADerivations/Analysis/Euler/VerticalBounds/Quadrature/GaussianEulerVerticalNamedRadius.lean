import IPRADerivations.Analysis.Gamma.Names.GaussianNamedGammaLateInput
import IPRADerivations.Analysis.Gamma.Names.PoleFree.Regularity.GaussianGammaRadiusOverlap
import IPRADerivations.Analysis.Euler.VerticalBounds.Projections.GaussianEulerVerticalNamedProjection

/-!
# Named Gamma observations in an enlarged numerical disk

The original frontend is kept at its own computed input radius. Exact
radius overlap transports its late-input estimate to any larger disk,
without changing either requested output tolerance or the supplied
continuity tolerance. The common disk for a name and its real projection
is the sum of their two original computed radii.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerVerticalNamedRadius

open_ipra
open GaussianNamedRightHalfPlane (source radius numerator denominator)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open GaussianNameEquivalence (cross_refl cross_symm)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaRealValues (axisF)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def commonRadius (f : PR 2) (x : PTm n) : PTm n := radius f x+radius (axisF f) x
def encodedData (f : PR 2) (r x A R : PTm n) : PTm n :=
  gammaData (numerator f r x) R (denominator f r x) (two*A)

ipra_subst commonRadius
ipra_subst encodedData

theorem source_enlarge (z S R B A : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaHalfPlaneInputContinuity.source z S B A)
    (hr : Γ ⊢[PRAAx] le S R) : Γ ⊢[PRAAx]
    GaussianGammaHalfPlaneInputContinuity.source z R B A :=
  .andI (.andI h.andE₁.andE₁ (.andI (.andI h.andE₁.andE₂.andE₁.andE₁
    (ComplexLogarithmRemainder.bounded_mono h.andE₁.andE₂.andE₁.andE₂
      (LeanProofs.IPRA.mul_le_mul_right B hr))) h.andE₁.andE₂.andE₂)) (le_trans h.andE₂ hr)

theorem original_independent_rate (f : PR 2) (s r x A R : PTm n)
    (h : Γ ⊢[PRAAx] GaussianNamedGammaLateInput.input f s r x A)
    (hr : Γ ⊢[PRAAx] le (radius f x) R) : Γ ⊢[PRAAx]
    independentRate (GaussianNamedGamma.nameF f) gammaF (GaussianNamedGamma.data x A)
      (encodedData f r x A R) one (unit s) := by
  have hs := GaussianNamedGammaLateInput.encoded_source f s r x A h
  have enlarged := source_enlarge _ _ R _ _ hs hr
  have overlap := GaussianGammaRadiusOverlap.original_Gamma_overlap _ _ R _ one (two*A) one (two*A)
    (GaussianGammaHalfPlaneInputContinuity.reciprocal_source _ _ _ _ hs)
    (GaussianGammaHalfPlaneInputContinuity.reciprocal_source _ _ _ _ enlarged)
  exact GaussianNamedRateTransport.transport (GaussianNamedGamma.nameF f) gammaF (GaussianNamedGamma.nameF f) gammaF
    _ _ _ _ one (unit s) (unit_positive s) (GaussianNamedGammaLateInput.original_independent_rate f s r x A h)
    (cross_refl _ _ (GaussianNamedGamma.name_regular f x A h.andE₁)) (cross_symm _ _ _ _ overlap)

theorem original_observations (f : PR 2) (p q s r x A R : PTm n)
    (h : Γ ⊢[PRAAx] GaussianNamedGammaLateInput.input f s r x A)
    (hr : Γ ⊢[PRAAx] le (radius f x) R) : Γ ⊢[PRAAx]
    GaussianRationalMetric.distanceBounded
      (ap2 (GaussianNamedGamma.nameF f) p (GaussianNamedGamma.data x A))
      (ap2 gammaF q (encodedData f r x A R))
      (rateNumerator one (unit s) p q) (rateDenominator (unit s) p q) :=
  GaussianNamedInverseRate.rate_at _ _ _ _ _ _ p q (original_independent_rate f s r x A R h hr)

theorem common_radius_bounds (f : PR 2) (x : PTm n) : Γ ⊢[PRAAx]
    le (radius f x) (commonRadius f x) ⋏ le (radius (axisF f) x) (commonRadius f x) :=
  .andI (le_add_right _ _) (le_add_left _ _)

theorem original_named_Gamma_enlarged_disk_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((GaussianNamedGammaLateInput.input f (var 0) (var 1) (var 2) (var 3) ⋏ le (radius f (var 2)) (var 4)) ⟶
      independentRate (GaussianNamedGamma.nameF f) gammaF (GaussianNamedGamma.data (var 2) (var 3))
        (encodedData f (var 1) (var 2) (var 3) (var 4)) one (unit (var 0))) :=
  closeUniv 5 (.impI (original_independent_rate f _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerVerticalNamedRadius
