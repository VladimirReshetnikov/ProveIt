import IPRADerivations.Analysis.Stirling.AllOrders.Logarithms.GaussianStirlingAllOrderLogRateFromStrict

/-!
# Exact power budgets for the multiplicative truncation theorem

For A/B at least one, a higher inverse power can be weakened to the
requested truncation degree. The denominator of a fixed coefficient
can be discarded while retaining its numerator as the error constant.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderLogRateBudget

open_ipra
open GaussianStirlingNames (source)
open GaussianStirlingExpansionConditionalError (logRate)
open GaussianStirlingAllOrderLogRateTransport (errorOrders)
open GaussianStirlingAllOrderLogRateFromStrict (log_rate_weaken)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem higher_inverse_power (K D A B j k : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hBA : Γ ⊢[PRAAx] le B A) : Γ ⊢[PRAAx]
    le ((K*pw B (j+k))*pw A j) ((K*pw B j)*(D*pw A (j+k))) := by
  have h := pw_le_pw k hBA
  have e := natEq (pw_add (Γ := Γ) B j k)
  have f := natEq (pw_add (Γ := Γ) A j k)
  ipra_le 𝔞 K*𝔞 (pw B j)*𝔞 (pw A j)*(sl h+𝔞 (pw A k)*sl hD) using
    rw [e,f]
    ring

theorem higher_log_rate (d : ℕ) (A B x K D k : PTm n) (hs : Γ ⊢[PRAAx] source A B)
    (hD : Γ ⊢[PRAAx] le one D) (hBA : Γ ⊢[PRAAx] le B A)
    (h : Γ ⊢[PRAAx] errorOrders d A B x
      (K*pw B (succ (num d)+k)) (D*pw A (succ (num d)+k))) : Γ ⊢[PRAAx] logRate d A B x K :=
  log_rate_weaken d A B x _ _ K hs
    (GaussianRationalHorner.positive_product _ _ hD (GaussianFactorBudget.power_positive _ _ hs.andE₁))
    (higher_inverse_power K D A B (succ (num d)) k hD hBA) h

theorem actual_higher_inverse_power_budget_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (le one (var 1) ⟶ le (var 3) (var 2) ⟶
        le ((var 0*pw (var 3) (var 4+var 5))*pw (var 2) (var 4))
          ((var 0*pw (var 3) (var 4))*(var 1*pw (var 2) (var 4+var 5)))) :=
  closeUniv 6 (.impI (.impI (higher_inverse_power _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderLogRateBudget
