import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianRootApproximationWitness

/-!
# Exact finite budgets for root membership and its converse

The source's forward witness has enough margin for the point-sample error.
In the converse, a cut observation and point-name comparison give a hit at
2^(-s)+4·2^(-m). The actual finite residual estimate then has the original
normalized V_s bound plus a single dyadic slack coefficient. Every number
and denominator is internal. These are derived arithmetic bounds, not
precision, membership, or vanishing assumptions.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRootMembershipBudget

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (unit)
open LeanProofs.IPRA.Analysis.GaussianRootSchedule (four coefficientConstant toleranceDenominator)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def slackCoefficient (c M : PTm n) : PTm n := four*M+two*c
@[simp] theorem subst_slackCoefficient {m : ℕ} (σ : Fin n → PTm m) (c M : PTm n) :
    Syn.subst σ (slackCoefficient c M) = slackCoefficient (Syn.subst σ c) (Syn.subst σ M) := by simp [slackCoefficient]

theorem coefficient_constant_monotone (N R U : PTm n) (hRU : Γ ⊢[PRAAx] le R U) : Γ ⊢[PRAAx]
    le (coefficientConstant N R) (coefficientConstant N U) :=
  le_mul_mono (le_refl N) (pw_le_pw (PTm.pred N) hRU)

theorem unit_add_one (k : PTm n) : Γ ⊢[PRAAx] unit (k+one) ≐ two*unit k :=
  (congrAp2 powF (by ipra_ring : Γ ⊢[PRAAx] k+one ≐ succ k) (.eqRefl two)).eqTrans
    ((pw_succ two k).eqTrans (mul_comm _ _))

theorem unit_monotone (s t : PTm n) (hst : Γ ⊢[PRAAx] le s t) : Γ ⊢[PRAAx] le (unit s) (unit t) :=
  GaussianFactorBudget.power_monotone_length _ _ _ (le_succ_self one) hst

theorem stage_denominator_lower (N R t m : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hmt : Γ ⊢[PRAAx] le m t) : Γ ⊢[PRAAx]
    le (unit m) (toleranceDenominator N R t) :=
  unit_monotone _ _ (le_trans hmt (GaussianRootSchedule.precision_ge_index N R t hN))

/-- Exactly 2^(-k-1)+2^(-s)≤2^(-k), at the source's actual s≥k+1. -/
theorem forward_point_error_budget (k s : PTm n) (hs : Γ ⊢[PRAAx] le (k+one) s) : Γ ⊢[PRAAx]
    le ((unit s+unit (k+one))*unit k) (unit (k+one)*unit s) := by
  have first := mul_le_mul_right (unit k) (unit_monotone _ _ hs)
  have sum := add_le_add₂ first (le_refl (unit k*unit s))
  have h := natEq (unit_add_one (Γ := Γ) k)
  refine le_congr ?_ ?_ sum
  · ipra_ring
  · apply deriveNat
    ipra_simps
    rw [h]
    ring

/-- The exact natural cross-product for transferring a cut hit from the
m+2 point sample to sample s. Only 2^m≤2^(m+2) is used. -/
theorem cut_point_transfer_budget (d h K : PTm n) (hK : Γ ⊢[PRAAx] le h K) : Γ ⊢[PRAAx]
    le (((d+K)*(h*h)+(h+two*h)*(d*K))*(d*h))
      ((h+four*d)*((d*K)*(h*h))) := by
  have scale := mul_le_mul_right (d*d*h*h) hK
  have sum := add_le_add₂ scale (le_refl (d*K*h*h*h+(two+one)*d*d*K*h*h))
  exact le_congr (by ipra_ring) (by unfold four; ipra_ring) sum

/-- At a hit of radius 1/d+4/h, the actual source residual is bounded by
(C+M)/d+(4M+2c)/h, when c=C_R≤C=C_U and h≤D=2^E(t). -/
theorem converse_residual_budget (c C M d h D : PTm n)
    (hc : Γ ⊢[PRAAx] le c C) (hD : Γ ⊢[PRAAx] le h D) : Γ ⊢[PRAAx]
    le ((M*(h+four*d)*(D*d)+c*(two*d+D)*(d*h))*(d*h))
      (((C+M)*h+slackCoefficient c M*d)*((d*h)*(D*d))) := by
  have first := le_mul_mono (add_le_add₂ (le_refl M) hc) (le_refl (h*D))
  have second := mul_le_mul_right (two*c*d) hD
  have inner : Γ ⊢[PRAAx] le
      ((M+c)*h*D+four*M*d*D+two*c*d*h)
      (((C+M)*h+slackCoefficient c M*d)*D) :=
    le_congr (by ipra_ring) (by unfold slackCoefficient; ipra_ring)
      (add_le_add₂ (add_le_add₂ first (le_refl (four*M*d*D))) second)
  exact le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (d*d*h) inner)

theorem forward_point_error_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (var 0+one) (var 1) ⟶ le ((unit (var 1)+unit (var 0+one))*unit (var 0))
      (unit (var 0+one)*unit (var 1))) := closeUniv 2 (.impI (forward_point_error_budget _ _ Prf.hyp0))

theorem cut_point_transfer_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 1) (var 2) ⟶
      le (((var 0+var 2)*(var 1*var 1)+(var 1+two*var 1)*(var 0*var 2))*(var 0*var 1))
        ((var 1+four*var 0)*((var 0*var 2)*(var 1*var 1)))) :=
  closeUniv 3 (.impI (cut_point_transfer_budget _ _ _ Prf.hyp0))

theorem converse_residual_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (var 0) (var 1) ⟶ le (var 4) (var 5) ⟶
      le ((var 2*(var 4+four*var 3)*(var 5*var 3)+var 0*(two*var 3+var 5)*(var 3*var 4))*(var 3*var 4))
        (((var 1+var 2)*var 4+slackCoefficient (var 0) (var 2)*var 3)*((var 3*var 4)*(var 5*var 3)))) :=
  closeUniv 6 (.impI (.impI (converse_residual_budget _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRootMembershipBudget
