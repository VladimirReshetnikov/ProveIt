import IPRADerivations.AnalyticNumberTheory.ZetaFiniteContract
import IPRADerivations.Analysis.Polynomials.GaussianCoefficientNameBounds
import IPRADerivations.Core.CommonLemmas

/-!
# Dyadic brackets of positive integer Barnes radii

The bounded ceiling-logarithm search on r+1 supplies the first power
of two strictly above r. Its predecessor gives the left endpoint of
the dyadic interval and preserves any certified lower dyadic threshold.
-/

set_option autoImplicit false
set_option maxHeartbeats 550000

namespace LeanProofs.IPRA.Analysis.BarnesDyadicRadius

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.ZetaFiniteContract (clog clog_spec clog_least)
open LeanProofs.IPRA.Common (le_of_lt_succ lt_succ_of_le pred_lt)
open GaussianCoefficientNameBounds (unit)
open GaussianFactorBudget (power_monotone_length)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def index (r : PTm n) : PTm n := pred (clog (succ r))

@[simp] theorem subst_index {m : ℕ} (σ : Fin n → PTm m) (r : PTm n) :
    Syn.subst σ (index r) = index (Syn.subst σ r) := by simp [index]

private theorem ceiling_positive (r : PTm n) (hr : Γ ⊢[PRAAx] le one r) :
    Γ ⊢[PRAAx] clog (succ r) ≐ succ (index r) := by
  let k := clog (succ r)
  have fit := (clog_spec (Γ := Γ) (succ r)).andE₁
  refine .orE (zero_or_succ k) ?_ Prf.hyp0
  have collapse : (k ≐ zero) :: Γ ⊢[PRAAx] (pw two k) ≐ one :=
    (congrAp2 powF Prf.hyp0 (.eqRefl two)).eqTrans (pw_zero two)
  exact le_lt_absurd _ (le_congr (.eqRefl _) collapse fit.wk) (lt_succ_of_le hr.wk)

theorem bracket (r : PTm n) (hr : Γ ⊢[PRAAx] le one r) :
    Γ ⊢[PRAAx] le (unit (index r)) r ⋏ lt r (unit (succ (index r))) := by
  have clk := ceiling_positive r hr
  have below := clog_least (pred_lt clk)
  have upper := (clog_spec (Γ := Γ) (succ r)).andE₁
  exact .andI (le_of_lt_succ below) (le_congr (.eqRefl _) (congrAp2 powF clk (.eqRefl two)) upper)

theorem threshold_le_index (r J : PTm n) (hr : Γ ⊢[PRAAx] le one r)
    (hJ : Γ ⊢[PRAAx] le (unit J) r) : Γ ⊢[PRAAx] le J (index r) := by
  let i := index r
  refine .orE (lt_or_le i J) ?_ Prf.hyp0
  have later : (lt i J) :: Γ ⊢[PRAAx] le (unit (succ i)) (unit J) :=
    power_monotone_length two (succ i) J (le_succ_self one) Prf.hyp0
  exact le_lt_absurd _ (le_trans later hJ.wk) (bracket r hr.wk).andE₂

theorem actual_Barnes_dyadic_radius_bracket_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (le one (var 0) ⟶ le (unit (index (var 0))) (var 0) ⋏ lt (var 0) (unit (succ (index (var 0))))) :=
  closeUniv 1 (.impI (bracket _ Prf.hyp0))

theorem actual_Barnes_dyadic_radius_threshold_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (le one (var 0) ⟶ le (unit (var 1)) (var 0) ⟶ le (var 1) (index (var 0))) :=
  closeUniv 2 (.impI (.impI (threshold_le_index _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.BarnesDyadicRadius
