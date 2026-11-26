import IPRADerivations.Analysis.Euler.Logarithms.GaussianEulerLogarithmicDerivative
import IPRADerivations.Analysis.Euler.Logarithms.GaussianEulerLogarithmicZeroIdentification
import IPRADerivations.Analysis.Names.Rates.GaussianNamedDifferenceQuotientProperness
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateTransport

/-!
# The original Gamma divided difference has the first Euler derivative

Both endpoints are the original Gamma program, at the literal native
shifted parameter and at the original base parameter. The already proved
order-zero Euler identification replaces each endpoint in the actual
divided-difference program. Exact name-rate transport retains the same
requested derivative accuracy and both independent observation errors.
No Gamma derivative or endpoint equality is supplied as a premise.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerFirstDerivative

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaReciprocalInverse (gammaF gammaData gamma_regular)
open GaussianEulerParameterExponentialIncrement (shifted)
open GaussianEulerLogarithmicImproperName (data name_regular)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_refl)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalMetric (distanceBounded)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "I" => GaussianEulerLogarithmicImproperName.nameF
local notation "QΓ" => GaussianNamedDifferenceQuotient.nameF gammaF gammaF
local notation "QI" => GaussianNamedDifferenceQuotient.nameF I I

def source (p z R B A h D : PTm n) : Fm PTm n :=
  GaussianEulerLogarithmicDerivative.source p zero z R B A h D ⋏ le one R
def quotientData (z R B A h D : PTm n) : PTm n :=
  GaussianNamedDifferenceQuotient.data gammaF gammaF
    (gammaData (shifted z B h D) (R+one) (B*D) (two*A)) (gammaData z R B A) h D

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (p z R B A h D : PTm n) :
    (source p z R B A h D).subst σ = source (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ h) (Syn.subst σ D) := by simp [source]
@[simp] theorem subst_quotientData {m : ℕ} (σ : Fin n → PTm m) (z R B A h D : PTm n) :
    Syn.subst σ (quotientData z R B A h D) = quotientData (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ h) (Syn.subst σ D) := by simp [quotientData]

theorem base_source (p z R B A h D : PTm n) (hs : Γ ⊢[PRAAx] source p z R B A h D) : Γ ⊢[PRAAx]
    GaussianEulerIntegralGammaIdentification.source z R B A := .andI hs.andE₁.andE₁.andE₁ hs.andE₂

theorem shifted_source (p z R B A h D : PTm n) (hs : Γ ⊢[PRAAx] source p z R B A h D) : Γ ⊢[PRAAx]
    GaussianEulerIntegralGammaIdentification.source (shifted z B h D) (R+one) (B*D) (two*A) :=
  .andI (GaussianEulerLogarithmicContinuity.shifted_certificate (p+num 6) one z R B A h D hs.andE₁.andE₁)
    (le_trans hs.andE₂ (le_add_right R one))

theorem original_quotient_proper (p z R B A h D : PTm n) (hs : Γ ⊢[PRAAx] source p z R B A h D) : Γ ⊢[PRAAx]
    crossEquivalent QI QΓ (GaussianEulerLogarithmicDerivative.quotientData zero z R B A h D) (quotientData z R B A h D) := by
  have base := base_source p z R B A h D hs
  have moved := shifted_source p z R B A h D hs
  have leftI := name_regular zero (shifted z B h D) (R+one) (B*D) (two*A) moved.andE₁
  have rightI := name_regular zero z R B A base.andE₁
  have leftΓ := gamma_regular _ _ _ one _ (GaussianGammaHalfPlaneInputContinuity.reciprocal_source _ _ _ _ moved)
  have rightΓ := gamma_regular _ _ _ one _ (GaussianGammaHalfPlaneInputContinuity.reciprocal_source _ _ _ _ base)
  exact GaussianNamedDifferenceQuotientProperness.proper I gammaF I gammaF _ _ _ _ h D leftI leftΓ rightI rightΓ
    (GaussianEulerLogarithmicZeroIdentification.original_logarithmic_order_zero_is_Gamma _ _ _ _ moved)
    (GaussianEulerLogarithmicZeroIdentification.original_logarithmic_order_zero_is_Gamma _ _ _ _ base)

theorem quotient_regular (p z R B A h D : PTm n) (hs : Γ ⊢[PRAAx] source p z R B A h D) : Γ ⊢[PRAAx]
    pointCN QΓ (quotientData z R B A h D) :=
  GaussianNamedDifferenceQuotient.name_regular gammaF gammaF _ _ h D
    (.andI (gamma_regular _ _ _ one _ (GaussianGammaHalfPlaneInputContinuity.reciprocal_source _ _ _ _ (shifted_source p z R B A h D hs)))
      (.andI (gamma_regular _ _ _ one _ (GaussianGammaHalfPlaneInputContinuity.reciprocal_source _ _ _ _ (base_source p z R B A h D hs)))
        (GaussianEulerLogarithmicDerivative.quotient_input p zero z R B A h D hs.andE₁).andE₂.andE₂))

/-- The actual original Gamma divided difference converges to the original
first logarithmic Euler integral with the same independent-observation rate. -/
theorem original_first_derivative_rate (p z R B A h D : PTm n) (hs : Γ ⊢[PRAAx] source p z R B A h D) : Γ ⊢[PRAAx]
    independentRate QΓ I (quotientData z R B A h D) (data one z R B A) one (unit p) :=
  GaussianNamedRateTransport.transport QI I QΓ I _ _ _ _ one (unit p) (unit_positive p)
    (GaussianEulerLogarithmicDerivative.original_derivative_rate p zero z R B A h D hs.andE₁)
    (cross_symm _ _ _ _ (original_quotient_proper p z R B A h D hs))
    (cross_refl I (data one z R B A) (name_regular one z R B A (base_source p z R B A h D hs).andE₁))

theorem original_observations (q v p z R B A h D : PTm n) (hs : Γ ⊢[PRAAx] source p z R B A h D) : Γ ⊢[PRAAx]
    distanceBounded (ap2 QΓ q (quotientData z R B A h D)) (ap2 I v (data one z R B A))
      (rateNumerator one (unit p) q v) (rateDenominator (unit p) q v) :=
  GaussianNamedInverseRate.rate_at QΓ I _ _ _ _ q v (original_first_derivative_rate p z R B A h D hs)

theorem actual_original_Gamma_first_Euler_derivative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      independentRate QΓ I (quotientData (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
        (data one (var 1) (var 2) (var 3) (var 4)) one (unit (var 0))) :=
  closeUniv 7 (.impI (original_first_derivative_rate _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaEulerFirstDerivative
