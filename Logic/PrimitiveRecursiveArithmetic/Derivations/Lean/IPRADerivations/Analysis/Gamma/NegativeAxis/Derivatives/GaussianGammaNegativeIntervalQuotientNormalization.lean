import IPRADerivations.Analysis.Gamma.NegativeAxis.Derivatives.GaussianGammaNegativeIntervalDerivativeTarget
import IPRADerivations.Analysis.Names.Rates.Perturbations.GaussianNamedDifferenceRate
import IPRADerivations.Analysis.Names.FiniteOperations.Products.GaussianNamedMultiplyRate
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateTransport

/-!
# Normalizing a negative Gamma difference quotient

Multiplying a quotient estimate by the original reciprocal Gamma name scales
its leading error by a uniform bound on that reciprocal. The normalized
derivative target is the original negative-interval digamma name.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalQuotientNormalization

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeIntervalDerivativeTarget (reciprocalData target_regular reciprocal_regular normalized_target)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U all_samples_bounded)
open GaussianNameEquivalence (cross_refl cross_symm)
open GaussianNamedDifferenceRate (self_rate rate_parameters_congr)
open GaussianNamedInverseRate (independentRate)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "P" => GaussianGammaC7Name.nameF
local notation "T" => GaussianGammaNegativeIntervalDerivativeTarget.nameF
local notation "targetData" => GaussianGammaNegativeIntervalDerivativeTarget.data
local notation "S" => GaussianGammaNegativeCriticalEndpoints.nameF
local notation "digammaData" => GaussianGammaNegativeCriticalEndpoints.nameData

theorem normalize_rate (QF : PR 2) (q a b N A B : PTm n)
    (h : Γ ⊢[PRAAx] guard a b) (hq : Γ ⊢[PRAAx] pointCN QF q)
    (hB : Γ ⊢[PRAAx] le one B)
    (hRate : Γ ⊢[PRAAx] independentRate QF T q (targetData a b N) A B) :
    Γ ⊢[PRAAx] independentRate (multiplyF P QF) S
      (multiplyData P QF (reciprocalData a b N) q) (digammaData a b N)
      (U P (reciprocalData a b N)*A) B := by
  let x := reciprocalData a b N
  let y := targetData a b N
  let R := U P x
  let M := U QF q
  have hp := reciprocal_regular a b N h
  have ht := target_regular a b N h
  have productRate := GaussianNamedMultiplyRate.independent_rate P QF P T x q x y zero one A B M R
    (le_refl one) hB hp hq hp ht (all_samples_bounded QF q hq) (all_samples_bounded P x hp)
    (self_rate P x hp) hRate
  have fixedRate := rate_parameters_congr (multiplyF P QF) (multiplyF P T)
    (multiplyData P QF x q) (multiplyData P T x y)
    (GaussianNamedMultiplyRate.leadingNumerator zero one A B M R)
    (GaussianNamedMultiplyRate.leadingDenominator one B) (R*A) B
    (by unfold GaussianNamedMultiplyRate.leadingNumerator; ipra_ring)
    (by unfold GaussianNamedMultiplyRate.leadingDenominator; ipra_ring) productRate
  exact GaussianNamedRateTransport.transport (multiplyF P QF) (multiplyF P T) (multiplyF P QF) S
    (multiplyData P QF x q) (multiplyData P T x y) (multiplyData P QF x q) (digammaData a b N)
    (R*A) B hB fixedRate
    (cross_refl _ _ (multiply_fast P QF x q hp hq))
    (cross_symm _ _ _ _ (normalized_target a b N h))

theorem actual_normalized_negative_interval_quotient_rate_closed (QF : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      ((guard (var 1) (var 2) ⋏ (pointCN QF (var 0) ⋏
        (le one (var 5) ⋏ independentRate QF T (var 0) (targetData (var 1) (var 2) (var 3)) (var 4) (var 5)))) ⟶
        independentRate (multiplyF P QF) S
          (multiplyData P QF (reciprocalData (var 1) (var 2) (var 3)) (var 0))
          (digammaData (var 1) (var 2) (var 3))
          (U P (reciprocalData (var 1) (var 2) (var 3))*var 4) (var 5)) :=
  closeUniv 6 (.impI (normalize_rate QF _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalQuotientNormalization
