import IPRADerivations.Foundations.FiniteQueryTable

/-!
# Forward validity of a topologically ordered contract graph

Packet: `foundations/ipra_proof_carrying_observation_graphs_2026-11-15`, `paper/sections/06_demand.tex`,
Theorem `thm:forward-validity` ("Forward graph validity"): if every source node is valid at its computed
demand, every node has a local contract and restriction is sound, then a topological forward run produces
every node valid at its computed demand, and every exported node is valid at its external request.
"Induct in topological order. At node `j`, all predecessors are valid at their computed demands by the
induction hypothesis."

The nodes are `j < L` in a topological order, so every predecessor of `j` is below `j`. Validity of node
`j` at its computed demand is a bit `v(j, x) ∈ {0, 1}` (the computed demands and the node certificates are
folded into `v` and the parameter `x`). The local contracts, together with the restriction of the
predecessors to their local demands, give the step hypothesis: if all nodes below `j` are valid,
`∏_{i<j} v(i) = 1`, then `v(j) = 1` (source nodes are the case without predecessors).

* `forward_all`: `∏_{i<L} v(i) = 1`, by quantifier-free induction along the order;
* `forward_node`: every node `j < L` is valid (`FiniteQueryTable.table_entry`);
* `exported`: an exported node `e < L` with a sound restriction from its computed demand to its external
  request (`v(e) = 1 → Q`) satisfies the request `Q`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.ForwardValidity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.FiniteQueryTable (table_entry)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The step hypothesis: for `j < L`, validity of every node below `j` gives validity of `j`. -/
abbrev Step (v : PTm 2) (L x : PTm n) : Fm PTm n :=
  Fm.all (lt (Syn.var 0) (Syn.shift L) ⟶
    (ap2 (prodF v) (Syn.var 0) (Syn.shift x) ≐ one) ⟶ (inst2 v (Syn.var 0) (Syn.shift x) ≐ one))

/-- The forward run: every node of the order is valid, `∏_{i<L} v(i) = 1`. -/
theorem forward_all (v : PTm 2) {L x : PTm n} (h : Γ ⊢[PRAAx] Step v L x) :
    Γ ⊢[PRAAx] ap2 (prodF v) L x ≐ one := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (Syn.var 0) (Syn.shift L) ⟶
      (ap2 (prodF v) (Syn.var 0) (Syn.shift x) ≐ one)) := by
    refine PRA.qfInd _ ⟨le_QF _ _, trivial⟩ ?_ ?_
    · simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, Syn.subst_var, Syn.inst_zero,
        Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact .impI (prod_zero v x)
    · simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, Syn.subst_var, Syn.repl_zero,
        subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      refine .impI ?_
      let Δ : List (Fm PTm (n + 1)) := le (succ (Syn.var 0)) (Syn.shift L) ::
        (le (Syn.var 0) (Syn.shift L) ⟶ (ap2 (prodF v) (Syn.var 0) (Syn.shift x) ≐ one)) :: Γ.map Fm.shift
      have hk : Δ ⊢[PRAAx] le (succ (Syn.var 0)) (Syn.shift L) := Prf.hyp0
      have ih : Δ ⊢[PRAAx] ap2 (prodF v) (Syn.var 0) (Syn.shift x) ≐ one :=
        Prf.impE Prf.hyp1 (le_trans (le_succ_self _) hk)
      have hv : Δ ⊢[PRAAx] inst2 v (Syn.var 0) (Syn.shift x) ≐ one :=
        Prf.impE (Prf.impE h.allOpen.wk.wk hk) ih
      have ps := prod_succ (Γ := Δ) v (Syn.var 0) (Syn.shift x)
      exact ps.eqTrans ((congrMul ih hv).eqTrans (one_mul _))
  have h2 := Prf.allE L hall
  simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at h2
  exact .impE h2 (le_refl L)

/-- `thm:forward-validity`: every node `j < L` is valid at its computed demand. -/
theorem forward_node (v : PTm 2) {L j x : PTm n} (h : Γ ⊢[PRAAx] Step v L x)
    (hbit : Γ ⊢[PRAAx] le (inst2 v j x) one) (hj : Γ ⊢[PRAAx] lt j L) :
    Γ ⊢[PRAAx] inst2 v j x ≐ one :=
  table_entry v hbit hj (forward_all v h)

/-- An exported node with a sound restriction to its external request satisfies the request. -/
theorem exported (v : PTm 2) {L e x : PTm n} {Q : Fm PTm n} (h : Γ ⊢[PRAAx] Step v L x)
    (hbit : Γ ⊢[PRAAx] le (inst2 v e x) one) (he : Γ ⊢[PRAAx] lt e L)
    (restrict : Γ ⊢[PRAAx] (inst2 v e x ≐ one) ⟶ Q) : Γ ⊢[PRAAx] Q :=
  .impE restrict (forward_node v h hbit he)

end LeanProofs.IPRA.Foundations.ForwardValidity
