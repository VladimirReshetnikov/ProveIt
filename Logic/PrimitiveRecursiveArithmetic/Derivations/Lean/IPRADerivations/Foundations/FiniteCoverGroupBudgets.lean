import IPRADerivations.Foundations.FiniteCoverAssignment
import IPRADerivations.Core.SubstCommand

/-!
# Variable group budgets for the actual first-cover assignment

A stored list supplies a separate numerical budget for each group. Bounds
on the sizes of the actual groups sum through the same verified cardinal
partition, with a common multiplier factored from the computed sum.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Foundations.FiniteCoverGroupBudgets

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open FiniteCoverAssignment (cover group groupSize group_length data sizeBody size_at total cardinal_partition)
open MasterCertificate (entry)
open SequenceComposition (length)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def body : PTm 2 := entry (var 1) (var 0)
def scaledBody : PTm 2 := fstT (var 1) * entry (sndT (var 1)) (var 0)
def budgetSum (K B : PTm n) : PTm n := ap2 (sumF body) K B
def scaledSum (K B m : PTm n) : PTm n := ap2 (sumF scaledBody) K (pairT m B)

def groupBudgets (f : PTm 3) (P K p B m : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift K) ⟶
    le (length (group f (Syn.shift P) (Syn.shift K) (Syn.shift p) (var 0)))
      (Syn.shift m * entry (Syn.shift B) (var 0)))

ipra_subst budgetSum
ipra_subst scaledSum
ipra_subst groupBudgets [Syn.subst_shift, Syn.shift_subst]

theorem entry_body_at (B i : PTm n) : inst2 body i B = entry B i := by simp [body,inst2]
theorem scaled_body_at (B m i : PTm n) : Γ ⊢[PRAAx] inst2 scaledBody i (pairT m B) ≐ m * entry B i := by
  simp only [scaledBody,inst2,LeanProofs.IPRA.PTm.subst_mul,subst_fstT,subst_sndT,
    MasterCertificate.subst_entry,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact congrMul (fst_pair _ _) (SequenceComposition.entry_congr (snd_pair _ _) (.eqRefl _))

theorem budget_sum_succ (K B : PTm n) : Γ ⊢[PRAAx] budgetSum (succ K) B ≐ budgetSum K B + entry B K := by
  simpa only [budgetSum,entry_body_at] using sum_succ' (Γ := Γ) body K B

theorem scaled_sum_succ (K B m : PTm n) : Γ ⊢[PRAAx] scaledSum (succ K) B m ≐ scaledSum K B m + m*entry B K :=
  (sum_succ' scaledBody K (pairT m B)).eqTrans (congrAdd (.eqRefl _) (scaled_body_at B m K))

theorem scale_budget_sum (K B m : PTm n) : Γ ⊢[PRAAx] scaledSum K B m ≐ m * budgetSum K B := by
  have all : Γ ⊢[PRAAx] .all (scaledSum (var 0) (Syn.shift B) (Syn.shift m) ≐
      Syn.shift m * budgetSum (var 0) (Syn.shift B)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq,subst_scaledSum,subst_budgetSum,LeanProofs.IPRA.PTm.subst_mul,
        Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (sum_zero _ _).eqTrans ((congrMul (.eqRefl _) (sum_zero _ _)).eqTrans (mul_zero _)).eqSymm
    · simp only [Fm.subst_eq,subst_scaledSum,subst_budgetSum,LeanProofs.IPRA.PTm.subst_mul,
        Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact (scaled_sum_succ _ _ _).eqTrans ((congrAdd Prf.hyp0 (.eqRefl _)).eqTrans
        ((mul_add _ _ _).eqSymm.eqTrans (congrMul (.eqRefl _) (budget_sum_succ _ _).eqSymm)))
  simpa only [Fm.subst_eq,subst_scaledSum,subst_budgetSum,LeanProofs.IPRA.PTm.subst_mul,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE K

theorem total_bound (f : PTm 3) (P K p B m : PTm n) (h : Γ ⊢[PRAAx] groupBudgets f P K p B m) :
    Γ ⊢[PRAAx] le (total f P K p) (m * budgetSum K B) := by
  have sums : Γ ⊢[PRAAx] le (total f P K p) (scaledSum K B m) := by
    refine sum_le_params (sizeBody f) scaledBody (data P K p) (pairT m B) K (.allI (.impI ?_))
    let Δ := lt (var 0) (Syn.shift K) :: Γ.map Fm.shift
    have localBound : Δ ⊢[PRAAx] le (length (group f (Syn.shift P) (Syn.shift K) (Syn.shift p) (var 0)))
        (Syn.shift m * entry (Syn.shift B) (var 0)) := .impE h.allOpen.wk Prf.hyp0
    have left := (size_at (Γ := Δ) f (Syn.shift P) (Syn.shift K) (Syn.shift p) (var 0)).eqTrans
      (group_length f (Syn.shift P) (Syn.shift K) (Syn.shift p) (var 0)).eqSymm
    simpa only [Δ,Syn.shift,FiniteCoverAssignment.subst_data,subst_pairT] using
      le_congr left.eqSymm (scaled_body_at (Syn.shift B) (Syn.shift m) (var 0)).eqSymm localBound
  exact le_congr (.eqRefl _) (scale_budget_sum K B m) sums

theorem cover_count (f : PTm 3) (P K p B m : PTm n) (hc : Γ ⊢[PRAAx] cover f P K p)
    (hb : Γ ⊢[PRAAx] groupBudgets f P K p B m) : Γ ⊢[PRAAx] le (length P) (m * budgetSum K B) :=
  le_congr (cardinal_partition f P K p hc) (.eqRefl _) (total_bound f P K p B m hb)

theorem actual_common_multiplier_budget_sum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (scaledSum (var 0) (var 1) (var 2) ≐ var 2 * budgetSum (var 0) (var 1)) :=
  closeUniv 3 (scale_budget_sum _ _ _)

theorem actual_variable_cover_budgets_closed (f : PTm 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (cover f (var 0) (var 1) (var 2) ⟶ groupBudgets f (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      le (length (var 0)) (var 4 * budgetSum (var 1) (var 3))) :=
  closeUniv 5 (.impI (.impI (cover_count f _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Foundations.FiniteCoverGroupBudgets
