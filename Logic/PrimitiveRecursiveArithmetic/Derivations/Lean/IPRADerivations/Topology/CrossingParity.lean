import IPRADerivations.Core.ParityArith

/-!
# Crossing parity of a polygonal chain

Packet: `topology/jordan_ipra_constructive_2026-11-15` (Section "Parity": the xor calculus of the
crossing rule, the xor cancellation in `lem:triangle`, `lem:replacement`). For a query point `p`
and a chain with vertices `v₀, …, v_N`, let `h(i) = [v_i is above p]`. An edge straddles the
height of `p` when `h(i) ⊕ h(i + 1) = 1`; the straddle count of edge `i` is taken here as
`h(i) + h(i + 1)`, whose parity is that xor. The statements hold for any body `h(i, x)` with a
parameter `x`, not only for bits.

* `straddle_parity`: `par (∑_{i<N} (h(i) + h(i+1)) + h(0) + h(N)) = 0`, by telescoping;
* `open_chain_parity`: the straddle parity of a chain is `par (h(0) + h(N))`, the xor of the
  indicators of its endpoints;
* `closed_chain_even`: for a closed chain, `h(N) = h(0)`, the straddle parity is zero. This is the
  case of `lem:triangle` in which all crossings lie on the same side of the query: every straddle
  is then a crossing, and the crossing parity vanishes;
* `triangle_xor`, `triangle_xor_bits`: the displayed cancellation
  `(a ⊕ b) ⊕ (b ⊕ c) ⊕ (c ⊕ a) = 0`;
* `reverse_edge`, `double_edge`, `concat_parity`: a contribution is unchanged by reversing an
  edge, two copies of an edge cancel, and the parity of a concatenation is the xor of the
  parities;
* `replacement`: chains whose crossing counts differ modulo two by a bounded sum of even triangle
  contributions have equal parities (`lem:replacement`).

The crossing test itself, the convexity argument of `lem:triangle`, and the sampling and
connection theorems are not formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Topology.CrossingParity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The straddle count of edge `i`: `h(i) + h(i + 1)`. -/
abbrev stB (h : PTm 2) : PTm 2 := h + Syn.subst ![succ (var 0), var 1] h

theorem inst2_st (h : PTm 2) (i x : PTm n) :
    inst2 (stB h) i x = inst2 h i x + inst2 h (succ i) x := by
  simp only [inst2, PTm.subst_add, Syn.subst_subst]
  congr 2
  funext j; fin_cases j <;> simp

/-! ## Telescoping -/

theorem tele_base (h : PTm 2) (x : PTm n) :
    Γ ⊢[PRAAx] par (ap2 (sumF (stB h)) zero x + inst2 h zero x + inst2 h zero x) ≐ zero := by
  have e : Γ ⊢[PRAAx] ap2 (sumF (stB h)) zero x + inst2 h zero x + inst2 h zero x ≐
      two * inst2 h zero x := by
    have z := natEq (sum_zero (Γ := Γ) (stB h) x)
    apply deriveNat; ipra_simps
    linear_combination z
  exact (congrAp1 parF e).eqTrans (par_double _)

theorem tele_step (h : PTm 2) {N x : PTm n}
    (ih : Γ ⊢[PRAAx] par (ap2 (sumF (stB h)) N x + inst2 h zero x + inst2 h N x) ≐ zero) :
    Γ ⊢[PRAAx] par (ap2 (sumF (stB h)) (succ N) x + inst2 h zero x + inst2 h (succ N) x) ≐ zero := by
  have s := sum_succ' (Γ := Γ) (stB h) N x
  rw [inst2_st] at s
  have e : Γ ⊢[PRAAx] ap2 (sumF (stB h)) (succ N) x + inst2 h zero x + inst2 h (succ N) x ≐
      (ap2 (sumF (stB h)) N x + inst2 h zero x + inst2 h N x) + two * inst2 h (succ N) x := by
    have a := natEq s
    apply deriveNat; ipra_simps
    linear_combination a
  exact (congrAp1 parF e).eqTrans ((par_add_two _ _).eqTrans ih)

/-- Variables: `0 = N` (induction), `1 = x`. -/
private abbrev teleF (h : PTm 2) : Fm PTm 2 :=
  par (ap2 (sumF (stB h)) (var 0) (var 1) + inst2 h zero (var 1) + inst2 h (var 0) (var 1)) ≐ zero

private theorem tele₀ (h : PTm 2) : ([] : List (Fm PTm 2)) ⊢[PRAAx] teleF h := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, subst_ap1, subst_ap2, PTm.subst_add, subst_inst2, Syn.subst_var,
      Syn.inst_zero, Syn.inst_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact tele_base h _
  · simp only [Fm.subst_eq, subst_ap1, subst_ap2, PTm.subst_add, subst_inst2, Syn.subst_var,
      Syn.repl_zero, repl_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact tele_step h Prf.hyp0

/-- `par (∑_{i<N} (h(i) + h(i+1)) + h(0) + h(N)) = 0`. -/
theorem straddle_parity (h : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] par (ap2 (sumF (stB h)) N x + inst2 h zero x + inst2 h N x) ≐ zero := by
  have i := inst (Γ := Γ) (tele₀ h) (![N, x] : Fin 2 → PTm n)
  simpa [subst_inst2] using i

/-- The straddle parity of a chain is the xor of the indicators of its endpoints. -/
theorem open_chain_parity (h : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] par (ap2 (sumF (stB h)) N x) ≐ par (inst2 h zero x + inst2 h N x) := by
  refine par_eq_of_add_even ((congrAp1 parF ?_).eqTrans (straddle_parity h N x))
  apply deriveNat; ipra_simps; ring

/-- A closed chain has an even number of straddles. -/
theorem closed_chain_even (h : PTm 2) {N x : PTm n} (hc : Γ ⊢[PRAAx] inst2 h N x ≐ inst2 h zero x) :
    Γ ⊢[PRAAx] par (ap2 (sumF (stB h)) N x) ≐ zero :=
  (open_chain_parity h N x).eqTrans
    ((congrAp1 parF (congrAdd (.eqRefl _) hc)).eqTrans (par_self_add _))

/-! ## The triangle and the xor calculus -/

/-- `(a + b) + (b + c) + (c + a)` is even. -/
theorem triangle_xor (a b c : PTm n) : Γ ⊢[PRAAx] par ((a + b) + (b + c) + (c + a)) ≐ zero := by
  have e : Γ ⊢[PRAAx] (a + b) + (b + c) + (c + a) ≐ two * (a + b + c) := by
    apply deriveNat; ipra_simps; ring
  exact (congrAp1 parF e).eqTrans (par_double _)

/-- `(a ⊕ b) ⊕ (b ⊕ c) ⊕ (c ⊕ a) = 0`, with `x ⊕ y = par (x + y)`. -/
theorem triangle_xor_bits (a b c : PTm n) :
    Γ ⊢[PRAAx] par (par (a + b) + par (b + c) + par (c + a)) ≐ zero :=
  (par_par_add₃ _ _ _).eqTrans (triangle_xor a b c)

/-- Reversing an edge does not change its contribution. -/
theorem reverse_edge (a b : PTm n) : Γ ⊢[PRAAx] par (a + b) ≐ par (b + a) :=
  congrAp1 parF (add_comm a b)

/-- Two copies of an edge cancel. -/
theorem double_edge (c : PTm n) : Γ ⊢[PRAAx] par (c + c) ≐ zero := par_self_add c

/-- The parity of a concatenation is the xor of the parities. -/
theorem concat_parity (P Q : PTm n) : Γ ⊢[PRAAx] par (P + Q) ≐ par (par P + par Q) := par_add P Q

/-- `lem:replacement`: if the crossing counts `P₁`, `P₂` of two chains differ modulo two by the
contributions `t(j, y)`, `j < M`, of triangles that each have even parity, then
`par P₁ = par P₂`. -/
theorem replacement (t : PTm 2) {P₁ P₂ C y M : PTm n}
    (h : Γ ⊢[PRAAx] P₁ + ap2 (sumF t) M y ≐ P₂ + two * C)
    (ht : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶ (par (inst2 t (var 0) (Syn.shift y)) ≐ zero))) :
    Γ ⊢[PRAAx] par P₁ ≐ par P₂ :=
  par_replacement h (sum_even_bounded t y M ht)

end LeanProofs.IPRA.Topology.CrossingParity
