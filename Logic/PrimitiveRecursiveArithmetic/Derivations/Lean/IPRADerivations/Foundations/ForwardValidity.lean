import IPRADerivations.Foundations.FiniteQueryTable
import IPRADerivations.Core.Header
import IPRADerivations.Core.BoundedSums

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

open_ipra
open LeanProofs.IPRA.Foundations.FiniteQueryTable (table_entry)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The step hypothesis: for `j < L`, validity of every node below `j` gives validity of `j`. -/
abbrev Step (v : PTm 2) (L x : PTm n) : Fm PTm n :=
  Fm.all (lt (Syn.var 0) (Syn.shift L) ⟶
    (ap2 (prodF v) (Syn.var 0) (Syn.shift x) ≐ one) ⟶ (inst2 v (Syn.var 0) (Syn.shift x) ≐ one))

/-- The forward run: every node of the order is valid, `∏_{i<L} v(i) = 1`. -/
theorem forward_all (v : PTm 2) {L x : PTm n} (h : Γ ⊢[PRAAx] Step v L x) :
    Γ ⊢[PRAAx] ap2 (prodF v) L x ≐ one := by
  let P : Fm PTm (n + 1) := ap2 (prodF v) (Syn.var 0) (Syn.shift x) ≐ one
  have atBound : Γ ⊢[PRAAx] P.subst (Syn.inst L) := by
    refine qfIndUpTo L trivial ?_ ?_
    · simpa [P] using prod_zero (Γ := Γ) v x
    · simp only [P, Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      refine .impI ?_
      let Δ := lt (Syn.var 0) (Syn.shift L) :: P :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] P := Prf.hyp1
      have hv : Δ ⊢[PRAAx] inst2 v (Syn.var 0) (Syn.shift x) ≐ one :=
        .impE (.impE h.allOpen.wk.wk Prf.hyp0) ih
      exact (prod_succ v (Syn.var 0) (Syn.shift x)).eqTrans ((congrMul ih hv).eqTrans (one_mul _))
  simpa [P] using atBound

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
