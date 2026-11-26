import IPRADerivations.Analysis.Stirling.GaussianStirlingDifferenceBounds
import IPRADerivations.Analysis.Stirling.GaussianStirlingIntegerLimit

/-!
# Cofinal limit of the actual Stirling integer names

The original finite Stirling endpoint estimates discharge the
uniform integer tail contract. The sampler at N=2^(p+4) is regular
and its distance from the original A(N) is bounded at independent
precision clocks by the exact rational 1/(12N) tail.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingOriginalIntegerLimit

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalMetric (distanceBounded)
open GaussianStirlingIntegerTail (integerTailContract contract_of_law point)
open GaussianStirlingIntegerLimit (nameF tailNumerator tailDenominator)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem integer_tail_contract : Γ ⊢[PRAAx] integerTailContract :=
  contract_of_law (fun i N hi => GaussianStirlingDifferenceBounds.endpoint_bounds N i one (.andI hi (le_refl one)))

theorem limit_regular (x : PTm n) : Γ ⊢[PRAAx] pointCN nameF x :=
  GaussianStirlingIntegerLimit.name_regular x integer_tail_contract

theorem actual_tail (p q i x : PTm n) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] distanceBounded (point p i) (ap2 nameF q x) (tailNumerator p q i) (tailDenominator p q i) :=
  GaussianStirlingIntegerLimit.tail_endpoint p q i x hi integer_tail_contract

theorem actual_Stirling_integer_limit_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (pointCN nameF (var 0)) :=
  closeUniv 1 (limit_regular _)

theorem actual_Stirling_integer_limit_exact_tail_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ distanceBounded (point (var 0) (var 2)) (ap2 nameF (var 1) (var 3))
      (tailNumerator (var 0) (var 1) (var 2)) (tailDenominator (var 0) (var 1) (var 2))) :=
  closeUniv 4 (.impI (actual_tail _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianStirlingOriginalIntegerLimit
