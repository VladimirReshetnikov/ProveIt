import IPRADerivations.Foundations.BackwardDemand
import IPRADerivations.Core.SumSplit
import IPRADerivations.Core.Header
import IPRADerivations.Core.BoundedSums

/-!
# The stage-dependent additive precision budget

A fixed PR loss reads the original stage and the persistent numerical data.
The existing backward schedule adds those losses in reverse order. Its
current demand plus the remaining ascending prefix sum equals the terminal
demand plus the full loss sum. The actual shifted finite sum gives the
budget at every stage, including the empty suffix at or past the horizon.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Foundations.BackwardDemandStageLoss

open_ipra
open LeanProofs.IPRA.Foundations.BackwardDemand
open LeanProofs.IPRA.Foundations.BoundedFormulas (BF)
open LeanProofs.IPRA.AnalyticNumberTheory.Totatives (monus_succ_of_lt)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def body (loss : PR 2) : PTm 2 := ap2 loss (var 0) (var 1)

def demandF (loss : PR 2) : PR 3 := PTm.toPR (var 1 + ap2 loss (var 0) (var 2))

def prefixLoss (loss : PR 2) (N x : PTm n) : PTm n := ap2 (sumF (body loss)) N x

def suffixLoss (loss : PR 2) (N t x : PTm n) : PTm n :=
  ap2 (sumF (offB (body loss))) (monus N t) (pairT t x)

@[simp] theorem subst_prefix {k : ℕ} (σ : Fin n → PTm k) (loss : PR 2) (N x : PTm n) :
    Syn.subst σ (prefixLoss loss N x) = prefixLoss loss (Syn.subst σ N) (Syn.subst σ x) := by
  simp [prefixLoss]

@[simp] theorem subst_suffix {k : ℕ} (σ : Fin n → PTm k) (loss : PR 2) (N t x : PTm n) :
    Syn.subst σ (suffixLoss loss N t x) = suffixLoss loss (Syn.subst σ N) (Syn.subst σ t) (Syn.subst σ x) := by
  simp [suffixLoss]

theorem demand_at (loss : PR 2) (t k x : PTm n) :
    Γ ⊢[PRAAx] ap3 (demandF loss) t k x ≐ k + ap2 loss t x := by
  have h := toPR_eq (Γ := Γ) (var 1 + ap2 loss (var 0) (var 2) : PTm 3) ![t, k, x]
  change Γ ⊢[PRAAx] ap3 (demandF loss) t k x ≐
    Syn.subst ![t, k, x] (var 1 + ap2 loss (var 0) (var 2) : PTm 3) at h
  simpa only [PTm.subst_add, subst_ap2, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using h

theorem prefix_zero (loss : PR 2) (x : PTm n) : Γ ⊢[PRAAx] prefixLoss loss zero x ≐ zero :=
  sum_zero (body loss) x

theorem prefix_succ (loss : PR 2) (N x : PTm n) :
    Γ ⊢[PRAAx] prefixLoss loss (succ N) x ≐ prefixLoss loss N x + ap2 loss N x := by
  simpa only [prefixLoss, body, inst2, subst_ap2, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one] using
    sum_succ' (Γ := Γ) (body loss) N x

theorem prefix_split (loss : PR 2) (N t x : PTm n) (ht : Γ ⊢[PRAAx] le t N) :
    Γ ⊢[PRAAx] prefixLoss loss N x ≐ prefixLoss loss t x + suffixLoss loss N t x :=
  (congrAp2 (sumF (body loss)) (eq_add_of_le ht) (.eqRefl x)).eqTrans
    (sum_split (body loss) t (monus N t) x)

theorem conservation_step (loss : PR 2) (N K j x : PTm n) (hj : Γ ⊢[PRAAx] lt j N)
    (ih : Γ ⊢[PRAAx] backward (demandF loss) N K j x + prefixLoss loss (monus N j) x ≐ K + prefixLoss loss N x) :
    Γ ⊢[PRAAx] backward (demandF loss) N K (succ j) x + prefixLoss loss (monus N (succ j)) x ≐
      K + prefixLoss loss N x := by
  let p := monus N (succ j)
  let B := backward (demandF loss) N K j x
  have oldPrefix : Γ ⊢[PRAAx] prefixLoss loss (monus N j) x ≐ prefixLoss loss p x + ap2 loss p x :=
    (congrAp2 (sumF (body loss)) (monus_succ_of_lt hj) (.eqRefl x)).eqTrans (prefix_succ loss p x)
  have update : Γ ⊢[PRAAx] backward (demandF loss) N K (succ j) x ≐ B + ap2 loss p x :=
    (backward_succ (demandF loss) N K j x).eqTrans (demand_at loss p B x)
  exact (congrAdd update (.eqRefl _)).eqTrans
    ((by ipra_ring : Γ ⊢[PRAAx] (B + ap2 loss p x) + prefixLoss loss p x ≐ B + (prefixLoss loss p x + ap2 loss p x)).eqTrans
      ((congrAdd (.eqRefl B) oldPrefix.eqSymm).eqTrans ih))

theorem backward_conservation (loss : PR 2) (N K j x : PTm n) (hj : Γ ⊢[PRAAx] le j N) :
    Γ ⊢[PRAAx] backward (demandF loss) N K j x + prefixLoss loss (monus N j) x ≐ K + prefixLoss loss N x := by
  let P : Fm PTm (n + 1) :=
    backward (demandF loss) (Syn.shift N) (Syn.shift K) (var 0) (Syn.shift x) +
      prefixLoss loss (monus (Syn.shift N) (var 0)) (Syn.shift x) ≐
      Syn.shift K + prefixLoss loss (Syn.shift N) (Syn.shift x)
  have atIndex : Γ ⊢[PRAAx] P.subst (Syn.inst j) := by
    refine qfIndAtMost hj trivial ?_ ?_
    · simp only [P, Fm.subst_eq, subst_backward, subst_prefix, PTm.subst_add, PTm.subst_monus,
        Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact congrAdd (backward_zero _ _ _ _) (congrAp2 (sumF (body loss)) (monus_zero N) (.eqRefl x))
    · simp only [P, Fm.subst_eq, subst_backward, subst_prefix, PTm.subst_add, PTm.subst_monus,
        Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      exact .impI (conservation_step loss _ _ (var 0) _ Prf.hyp0 Prf.hyp1)
  simpa only [P, Fm.subst_eq, subst_backward, subst_prefix, PTm.subst_add, PTm.subst_monus,
    Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using atIndex

theorem initial_budget (loss : PR 2) (N K x : PTm n) :
    Γ ⊢[PRAAx] horizon (demandF loss) N K zero x ≐ K + prefixLoss loss N x := by
  have h := backward_conservation (Γ := Γ) loss N K N x (le_refl N)
  have empty : Γ ⊢[PRAAx] prefixLoss loss (monus N N) x ≐ zero :=
    (congrAp2 (sumF (body loss)) (monus_self N) (.eqRefl x)).eqTrans (prefix_zero loss x)
  have e := (add_zero (Γ := Γ) (backward (demandF loss) N K N x)).eqSymm.eqTrans
    ((congrAdd (.eqRefl _) empty.eqSymm).eqTrans h)
  exact (backward_index_congr (demandF loss) N K x (monus_zero N)).eqTrans e

theorem horizon_in_range (loss : PR 2) (N K t x : PTm n) (ht : Γ ⊢[PRAAx] le t N) :
    Γ ⊢[PRAAx] horizon (demandF loss) N K t x ≐ K + suffixLoss loss N t x := by
  let d := monus N t
  let P := prefixLoss loss t x
  let S := suffixLoss loss N t x
  have split := eq_add_of_le ht
  have recovered : Γ ⊢[PRAAx] monus N d ≐ t :=
    (congrMonus split (.eqRefl d)).eqTrans (add_monus _ _)
  have h := backward_conservation loss N K d x (le_congr (.eqRefl d) split.eqSymm (le_add_left _ _))
  have lhs : Γ ⊢[PRAAx] horizon (demandF loss) N K t x + P ≐ K + prefixLoss loss N x :=
    (congrAdd (.eqRefl _) (congrAp2 (sumF (body loss)) recovered.eqSymm (.eqRefl x))).eqTrans h
  exact add_right_cancel (lhs.eqTrans ((congrAdd (.eqRefl K) (prefix_split loss N t x ht)).eqTrans
    (by ipra_ring : Γ ⊢[PRAAx] K + (P + S) ≐ (K + S) + P)))

theorem horizon_suffix (loss : PR 2) (N K t x : PTm n) :
    Γ ⊢[PRAAx] horizon (demandF loss) N K t x ≐ K + suffixLoss loss N t x := by
  refine .orE (lt_or_le N t) ?_ (horizon_in_range loss N K t x Prf.hyp0)
  have empty : lt N t :: Γ ⊢[PRAAx] monus N t ≐ zero := le_of_lt Prf.hyp0
  have left := (backward_index_congr (demandF loss) N K x empty).eqTrans (backward_zero _ _ _ _)
  have right : lt N t :: Γ ⊢[PRAAx] suffixLoss loss N t x ≐ zero :=
    (congrAp2 (sumF (offB (body loss))) empty (.eqRefl _)).eqTrans (sum_zero _ _)
  exact left.eqTrans ((congrAdd (.eqRefl K) right).eqTrans (add_zero K)).eqSymm

theorem stage_loss_transfer (A : BF) (loss : PR 2) (N K x : PTm n)
    (hstep : Γ ⊢[PRAAx] localStep A (demandF loss) N x)
    (hbase : Γ ⊢[PRAAx] observation A zero (K + prefixLoss loss N x) x) :
    Γ ⊢[PRAAx] observation A N K x :=
  transfer A (demandF loss) N K x
    (observation_demand_congr A zero x (initial_budget loss N K x).eqSymm hbase) hstep

theorem actual_initial_budget_closed (loss : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (horizon (demandF loss) (var 0) (var 1) zero (var 2) ≐ var 1 + prefixLoss loss (var 0) (var 2)) :=
  closeUniv 3 (initial_budget loss _ _ _)

theorem actual_suffix_budget_closed (loss : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (horizon (demandF loss) (var 0) (var 1) (var 2) (var 3) ≐ var 1 + suffixLoss loss (var 0) (var 2) (var 3)) :=
  closeUniv 4 (horizon_suffix loss _ _ _ _)

theorem actual_stage_loss_transfer_closed (A : BF) (loss : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (localStep A (demandF loss) (var 0) (var 2) ⟶
      observation A zero (var 1 + prefixLoss loss (var 0) (var 2)) (var 2) ⟶
      observation A (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (stage_loss_transfer A loss _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Foundations.BackwardDemandStageLoss
