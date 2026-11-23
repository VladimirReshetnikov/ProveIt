import IPRADerivations.Analysis.GaussianEulerSharpRealScheduleBudget

/-!
# Strict bounds for both leading terms in the literal sharp Euler rate

Both terms are strictly below 2^-(p+3). These are cleared inequalities
for the actual original fixed-tail ratio, with the same degree and
decay observation query as before.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerSharpReportTerms

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerSharpDegreeSchedule (degree coefficient)
open GaussianEulerSharpScheduleBudget (decayClock)
open GaussianBetaContiguousUpperTailBudget (fixedNumerator fixedDenominator fixed_denominator_positive)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem next_unit (p : PTm n) : Γ ⊢[PRAAx] unit (p+num 4) ≐ two*unit (p+num 3) :=
  ((congrAp2 powF (by ipra_ring : Γ ⊢[PRAAx] p+num 4 ≐ succ (p+num 3)) (.eqRefl two)).eqTrans
    (pw_succ two (p+num 3))).eqTrans (mul_comm _ _)

theorem coefficient_strict_budget (p R : PTm n) : Γ ⊢[PRAAx]
    lt (coefficient R*unit (p+num 3)) (degree p R) := by
  have hc : Γ ⊢[PRAAx] le one (coefficient R) :=
    le_of_eq_add (d := GaussianMonomialDecayQuadrature.cap (R+two)) (.eqRefl _)
  have hw := GaussianRationalHorner.positive_product _ _ hc (unit_positive (p+num 3))
  have gap : Γ ⊢[PRAAx] lt (coefficient R*unit (p+num 3)) (num 8*coefficient R*unit (p+num 3)) := by
    ipra_le 7*sl hw+6
  have actual : Γ ⊢[PRAAx] le (num 8*coefficient R*unit (p+num 3)) (degree p R) := by
    refine le_congr ?_ (.eqRefl _) (GaussianEulerSharpRealScheduleBudget.coefficient_quarter_budget p R)
    apply deriveNat
    have eq := natEq (next_unit (Γ := Γ) p)
    ipra_simps
    rw [eq]
    ring
  exact lt_of_lt_of_le gap actual

theorem fixed_tail_strict_budget (p R : PTm n) : Γ ⊢[PRAAx]
    lt (fixedNumerator (decayClock p R) R (degree p R)*unit (p+num 3))
      (fixedDenominator (decayClock p R) (degree p R)) := by
  let F := fixedNumerator (decayClock p R) R (degree p R)
  let E := fixedDenominator (decayClock p R) (degree p R)
  have actual : Γ ⊢[PRAAx] le (num 10*F*unit (p+num 3)) (num 8*E) := by
    refine le_congr ?_ (.eqRefl _) (GaussianEulerSharpRealScheduleBudget.fixed_tail_exact_budget p R)
    apply deriveNat
    have eq := natEq (next_unit (Γ := Γ) p)
    dsimp only [F]
    ipra_simps
    rw [eq]
    ring
  have he : Γ ⊢[PRAAx] le one E := fixed_denominator_positive _ _
  have gap : Γ ⊢[PRAAx] lt (num 8*E) (num 10*E) := by ipra_le 2*sl he+1
  refine .orE (lt_or_le (F*unit (p+num 3)) E) Prf.hyp0 ?_
  have backwards := mul_le_mul_right (num 10) (Prf.hyp0 : (_ :: Γ) ⊢[PRAAx] le E (F*unit (p+num 3)))
  exact le_lt_absurd _ (le_trans (le_congr (by ipra_ring) (by ipra_ring) backwards) actual.wk) gap.wk

theorem literal_sharp_Euler_report_terms_strict_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (coefficient (var 1)*unit ((var 0)+num 3)) (degree (var 0) (var 1)) ⋏
      lt (fixedNumerator (decayClock (var 0) (var 1)) (var 1) (degree (var 0) (var 1))*unit ((var 0)+num 3))
        (fixedDenominator (decayClock (var 0) (var 1)) (degree (var 0) (var 1)))) :=
  closeUniv 2 (.andI (coefficient_strict_budget _ _) (fixed_tail_strict_budget _ _))

end LeanProofs.IPRA.Analysis.GaussianEulerSharpReportTerms
