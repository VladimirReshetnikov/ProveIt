import IPRADerivations.Algebra.QuadraticTowerMultiplicationTable

/-!
# Exact scalar growth calculus for the actual changed-budget table

These are ordinary numerical induction laws of the SAME scalar growth
program. Composition, both monotonicities and inflation justify repeated
local height estimates. The multiplication dependency path satisfies
c(0)=1 and c(h+1)=2*c(h)+1; its growth fits the SAME actual table budget.
No height estimate for a table answer or its computed be value is assumed
or concluded by these scalar laws alone.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Algebra.QuadraticTowerGrowth

open_ipra
open QuadraticTowerScalarBudget (amp growth growthF growth_zero growth_succ majorant)
open QuadraticTowerMultiplicationTable (sourceCost budget budget_at)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem amp_congr {B C : PTm n} (h : Γ ⊢[PRAAx] B ≐ C) : Γ ⊢[PRAAx] amp B ≐ amp C :=
  congrMul (congrMul (.eqRefl _) h) h
theorem amp_mono {B C : PTm n} (h : Γ ⊢[PRAAx] le B C) : Γ ⊢[PRAAx] le (amp B) (amp C) :=
  le_congr (by unfold amp; ipra_ring) (by unfold amp; ipra_ring)
    (le_mul_mono (le_refl two) (le_mul_mono h h))
theorem amp_inflation (B : PTm n) : Γ ⊢[PRAAx] le B (amp B) := by
  refine .orE (zero_or_succ B) ?_ ?_
  · exact le_congr Prf.hyp0.eqSymm (.eqRefl _) (zero_le _)
  · have hp : ((B ≐ succ (pred B)) :: Γ) ⊢[PRAAx] le one B :=
      Order.zero_lt_of_eq_succ Prf.hyp0
    exact le_trans (le_congr (one_mul B) (.eqRefl _) (mul_le_mul_right B hp))
      (QuadraticTowerScalarBudget.square_le_amp B)
theorem growth_congr {t u B C : PTm n} (ht : Γ ⊢[PRAAx] t ≐ u) (hB : Γ ⊢[PRAAx] B ≐ C) :
    Γ ⊢[PRAAx] growth t B ≐ growth u C := congrAp2 growthF ht hB

def monotoneLaw (t B C : PTm n) : Fm PTm n := le (growth t B) (growth t C)
def inflationLaw (t B : PTm n) : Fm PTm n := le B (growth t B)
def compositionLaw (t u B : PTm n) : Fm PTm n := growth t (growth u B) ≐ growth (t+u) B
ipra_subst monotoneLaw
ipra_subst inflationLaw
ipra_subst compositionLaw

theorem growth_mono (t B C : PTm n) (hBC : Γ ⊢[PRAAx] le B C) : Γ ⊢[PRAAx] le (growth t B) (growth t C) := by
  have all : Γ ⊢[PRAAx] .all (monotoneLaw (var 0) (Syn.shift B) (Syn.shift C)) := by
    ipra_qfind (le_QF _ _) [subst_monotoneLaw]
    · exact le_congr (growth_zero B).eqSymm (growth_zero C).eqSymm hBC
    · exact le_congr (growth_succ _ _).eqSymm (growth_succ _ _).eqSymm (amp_mono Prf.hyp0)
  change Γ ⊢[PRAAx] monotoneLaw t B C
  simpa only [subst_monotoneLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE t
theorem growth_inflation (t B : PTm n) : Γ ⊢[PRAAx] le B (growth t B) := by
  have all : Γ ⊢[PRAAx] .all (inflationLaw (var 0) (Syn.shift B)) := by
    ipra_qfind (le_QF _ _) [subst_inflationLaw]
    · exact le_congr (.eqRefl _) (growth_zero B).eqSymm (le_refl B)
    · exact le_trans Prf.hyp0 (le_congr (.eqRefl _) (growth_succ _ _).eqSymm (amp_inflation _))
  change Γ ⊢[PRAAx] inflationLaw t B
  simpa only [subst_inflationLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE t

theorem composition_zero (u B : PTm n) : Γ ⊢[PRAAx] compositionLaw zero u B :=
  (growth_zero _).eqTrans (growth_congr (zero_add u).eqSymm (.eqRefl _))
theorem composition_step (t u B : PTm n) (ih : Γ ⊢[PRAAx] compositionLaw t u B) :
    Γ ⊢[PRAAx] compositionLaw (succ t) u B :=
  (growth_succ _ _).eqTrans ((amp_congr ih).eqTrans
    ((growth_succ _ _).eqSymm.eqTrans (growth_congr (succ_add t u).eqSymm (.eqRefl _))))
theorem growth_composition (t u B : PTm n) : Γ ⊢[PRAAx] growth t (growth u B) ≐ growth (t+u) B := by
  have all : Γ ⊢[PRAAx] .all (compositionLaw (var 0) (Syn.shift u) (Syn.shift B)) := by
    ipra_qfind [subst_compositionLaw]
    · exact composition_zero _ _
    · exact composition_step _ _ _ Prf.hyp0
  change Γ ⊢[PRAAx] compositionLaw t u B
  simpa only [subst_compositionLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE t
theorem growth_counter_mono (t u B : PTm n) (h : Γ ⊢[PRAAx] le t u) :
    Γ ⊢[PRAAx] le (growth t B) (growth u B) := by
  have e : Γ ⊢[PRAAx] monus u t+t ≐ u := (add_comm _ _).eqTrans (eq_add_of_le h).eqSymm
  exact le_congr (.eqRefl _) ((growth_composition (monus u t) t B).eqTrans
    (growth_congr e (.eqRefl _))) (growth_inflation (monus u t) (growth t B))

def path (h : PTm n) : PTm n := pred (pw two (succ h))
ipra_subst path [two, one]
theorem path_power (h : PTm n) : Γ ⊢[PRAAx] pw two (succ h) ≐ succ (path h) :=
  Foundations.RuntimeWordAppend.positive_form _
    (Foundations.RuntimeWordAppend.power_positive two (succ h) (le_succ_self one))
theorem path_zero : Γ ⊢[PRAAx] path (zero : PTm n) ≐ one :=
  (congrPred (pw_one two)).eqTrans (pred_succ one)
theorem path_succ (h : PTm n) : Γ ⊢[PRAAx] path (succ h) ≐ two*path h+one := by
  ipra_lc natEq (path_power (Γ := Γ) h)*2-natEq (path_power (Γ := Γ) (succ h))+natEq (pw_succ (Γ := Γ) two (succ h))
theorem path_increasing (h : PTm n) : Γ ⊢[PRAAx] le (path h) (path (succ h)) :=
  le_congr (.eqRefl _) (path_succ h).eqSymm
    (le_of_eq_add (d := path h+one) (by ipra_ring))
theorem path_le_cost (h : PTm n) : Γ ⊢[PRAAx] le (path h) (sourceCost h) := by
  have hp : Γ ⊢[PRAAx] le (path h) (pw two (succ h)) :=
    le_congr (.eqRefl _) (path_power h).eqSymm (le_succ_self _)
  have bases : Γ ⊢[PRAAx] le (two : PTm n) (PTm.num 8) :=
    le_of_eq_add (d := PTm.num 6) (by ipra_ring)
  have scale : Γ ⊢[PRAAx] le (one : PTm n) (PTm.num 1000) :=
    le_of_eq_add (d := PTm.num 999) (by ipra_ring)
  exact le_trans hp (le_trans (pw_le_pw (succ h) bases)
    (le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right _ scale)))

theorem path_growth_budget (h B D b : PTm n) (hb : Γ ⊢[PRAAx] le b B) :
    Γ ⊢[PRAAx] le (growth (path (succ h)) b) (budget h B D) :=
  le_congr (.eqRefl _) (budget_at h B D).eqSymm
    (le_trans (growth_mono _ _ _ hb)
      (le_trans (growth_counter_mono _ _ _ (path_le_cost (succ h)))
        (QuadraticTowerScalarBudget.growth_le_majorant _ _)))
theorem lower_path_budget (h B D b : PTm n) (hb : Γ ⊢[PRAAx] le b B) :
    Γ ⊢[PRAAx] le (growth (path h) b) (budget h B D) :=
  le_trans (growth_counter_mono _ _ _ (path_increasing h)) (path_growth_budget h B D b hb)
theorem twice_then_add (h B : PTm n) : Γ ⊢[PRAAx]
    amp (growth (path h) (growth (path h) B)) ≐ growth (path (succ h)) B :=
  (amp_congr (growth_composition _ _ _)).eqTrans
    ((growth_succ _ _).eqSymm.eqTrans
      (growth_congr ((by ipra_ring : Γ ⊢[PRAAx] succ (path h+path h) ≐ two*path h+one).eqTrans
        (path_succ h).eqSymm) (.eqRefl _)))

def pathF : PR 1 := PTm.toPR (path (var 0))
theorem path_program_at (h : PTm n) : Γ ⊢[PRAAx] ap1 pathF h ≐ path h := by
  simpa [pathF,ap1] using toPR_eq (Γ := Γ) (path (var 0) : PTm 1) ![h]

theorem actual_multiplication_path_base_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] path (zero : PTm 0) ≐ one := path_zero
theorem actual_multiplication_path_cost_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le (path (var 0)) (sourceCost (var 0))) := closeUniv 1 (path_le_cost _)
theorem actual_multiplication_path_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (ap1 pathF (var 0) ≐ path (var 0)) := closeUniv 1 (path_program_at _)
theorem actual_scalar_growth_composition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (growth (var 0) (growth (var 1) (var 2)) ≐ growth (var 0+var 1) (var 2)) := closeUniv 3 (growth_composition _ _ _)
theorem actual_scalar_growth_monotone_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 1) (var 2) ⟶ le (growth (var 0) (var 1)) (growth (var 0) (var 2))) :=
  closeUniv 3 (.impI (growth_mono _ _ _ Prf.hyp0))
theorem actual_scalar_growth_counter_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 0) (var 1) ⟶ le (growth (var 0) (var 2)) (growth (var 1) (var 2))) :=
  closeUniv 3 (.impI (growth_counter_mono _ _ _ Prf.hyp0))
theorem actual_scalar_growth_inflation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (var 1) (growth (var 0) (var 1))) := closeUniv 2 (growth_inflation _ _)
theorem actual_multiplication_path_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (path (succ (var 0)) ≐ two*path (var 0)+one) := closeUniv 1 (path_succ _)
theorem actual_multiplication_path_scalar_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 3) (var 1) ⟶ le (growth (path (succ (var 0))) (var 3)) (budget (var 0) (var 1) (var 2))) :=
  closeUniv 4 (.impI (path_growth_budget _ _ _ _ Prf.hyp0))
theorem actual_nested_lower_scalar_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 3) (var 1) ⟶ le (growth (path (var 0)) (var 3)) (budget (var 0) (var 1) (var 2))) :=
  closeUniv 4 (.impI (lower_path_budget _ _ _ _ Prf.hyp0))
theorem actual_two_lower_paths_and_add_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (amp (growth (path (var 0)) (growth (path (var 0)) (var 1))) ≐ growth (path (succ (var 0))) (var 1)) :=
  closeUniv 2 (twice_then_add _ _)

end LeanProofs.IPRA.Algebra.QuadraticTowerGrowth
