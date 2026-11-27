import IPRADerivations.Probability.Ninther

/-!
# The least reverse demand along a chain

Packets (`docs/proofs/foundations`): `ipra_kifc_framework_2026-11-15`, `ipra_kifc_framework_2026-11-16`,
`ipra_kifcr_framework_2026-11-16`, `ipra_kifcs_framework_2026-11-16`, Lemma `lem:demand-least` ("Least reverse
demand for an acyclic graph"): with requests defined backward by
`q_u = max(q_u^terminal, max_{u→v} d_{uv}(q_v))` for monotone demand transformers, the resulting vector
satisfies every terminal and edge inequality and is componentwise least among all satisfying vectors.

Here the graph is a chain, indexed by the remaining depth `j` (the node at depth `j + 1` has one edge to the
node at depth `j`): terminal requests `term(j, x)`, edge transformers `d(j, q, x)`, and

`rd 0 = term(0)`,  `rd (j + 1) = max(term(j + 1), d(j, rd j))`,

a primitive recursion with the maximum `mx a b = a + (b ∸ a)` of `Probability/Ninther`.

* `le_mx_left`, `le_mx_right`, `mx_lub`: `mx a b` is the least upper bound of `a` and `b`;
* `sound_term`, `sound_edge`: `term(j + 1) ≤ rd (j + 1)` and `d(j, rd j) ≤ rd (j + 1)`; `rd 0 = term(0)`
  (`rd_zero`);
* `least`: for monotone `d` (a rule) and any request vector `p(j, x)` with `term(0) ≤ p(0)`,
  `term(j + 1) ≤ p(j + 1)` and `d(j, p(j)) ≤ p(j + 1)` for all `j`: `rd j ≤ p(j)` for every `j`.

The general acyclic graph, where the maximum ranges over several out-edges, is not derived.
-/

namespace LeanProofs.IPRA.Foundations.ReverseDemand

open_ipra exports
open LeanProofs.IPRA.Probability.Ninther (mx mx_le mx_ge)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The maximum is the least upper bound -/

theorem le_mx_left (a b : PTm n) : Γ ⊢[PRAAx] le a (mx a b) := le_add_right a (monus b a)

theorem le_mx_right (a b : PTm n) : Γ ⊢[PRAAx] le b (mx a b) :=
  .orE (le_total a b) (le_congr (.eqRefl b) (Prf.eqSymm (mx_le Prf.hyp0)) (le_refl b))
    (le_congr (.eqRefl b) (Prf.eqSymm (mx_ge Prf.hyp0)) Prf.hyp0)

theorem mx_lub {a b c : PTm n} (ha : Γ ⊢[PRAAx] le a c) (hb : Γ ⊢[PRAAx] le b c) :
    Γ ⊢[PRAAx] le (mx a b) c :=
  .orE (le_total a b) (le_congr (Prf.eqSymm (mx_le Prf.hyp0)) (.eqRefl c) hb.wk)
    (le_congr (Prf.eqSymm (mx_ge Prf.hyp0)) (.eqRefl c) ha.wk)

/-! ## The backward recursion -/

/-- `d(j, q, x)`. -/
abbrev dAt (d : PTm 3) (j q x : PTm n) : PTm n := Syn.subst ![j, q, x] d

/-- Step of the recursion; variables `0 = j`, `1 = rd j`, `2 = x`. -/
abbrev rdStep (term : PTm 2) (d : PTm 3) : PTm 3 := mx (inst2 term (succ (var 0)) (var 2)) d

/-- The request at depth `0`. -/
abbrev rdInit (term : PTm 2) : PTm 1 := inst2 term zero (var 0)

/-- The reverse demand at depth `j`. -/
abbrev rd (term : PTm 2) (d : PTm 3) (j x : PTm n) : PTm n := ap2 (rec2 (rdInit term) (rdStep term d)) j x

section Demand

variable {term : PTm 2} {d : PTm 3}

theorem rd_zero (x : PTm n) : Γ ⊢[PRAAx] rd term d zero x ≐ inst2 term zero x := by
  have h := rec2_zero (Γ := Γ) (rdInit term) (rdStep term d) x
  simpa using h

theorem rd_succ (j x : PTm n) :
    Γ ⊢[PRAAx] rd term d (succ j) x ≐ mx (inst2 term (succ j) x) (dAt d j (rd term d j x) x) := by
  have h := rec2_succ (Γ := Γ) (rdInit term) (rdStep term d) j x
  have e : Syn.subst ![j, ap2 (rec2 (rdInit term) (rdStep term d)) j x, x] (rdStep term d) =
      mx (inst2 term (succ j) x) (dAt d j (rd term d j x) x) := by simp
  rw [e] at h
  exact h

/-- The terminal inequality: `term(j + 1) ≤ rd (j + 1)`. -/
theorem sound_term (j x : PTm n) : Γ ⊢[PRAAx] le (inst2 term (succ j) x) (rd term d (succ j) x) :=
  le_congr (.eqRefl _) (rd_succ j x).eqSymm (le_mx_left _ _)

/-- The edge inequality: `d(j, rd j) ≤ rd (j + 1)`. -/
theorem sound_edge (j x : PTm n) : Γ ⊢[PRAAx] le (dAt d j (rd term d j x) x) (rd term d (succ j) x) :=
  le_congr (.eqRefl _) (rd_succ j x).eqSymm (le_mx_right _ _)

/-! ## Leastness -/

variable {p : PTm 2}

theorem least_base {x : PTm n} (hp0 : Γ ⊢[PRAAx] le (inst2 term zero x) (inst2 p zero x)) :
    Γ ⊢[PRAAx] le (rd term d zero x) (inst2 p zero x) :=
  le_congr (rd_zero x).eqSymm (.eqRefl _) hp0

theorem least_step
    (hmono : ∀ {k : ℕ} {Θ : List (Fm PTm k)} (j q q' y : PTm k),
      (Θ ⊢[PRAAx] le q q') → (Θ ⊢[PRAAx] le (dAt d j q y) (dAt d j q' y)))
    {j x : PTm n} (ht : Γ ⊢[PRAAx] le (inst2 term (succ j) x) (inst2 p (succ j) x))
    (he : Γ ⊢[PRAAx] le (dAt d j (inst2 p j x) x) (inst2 p (succ j) x))
    (ih : Γ ⊢[PRAAx] le (rd term d j x) (inst2 p j x)) :
    Γ ⊢[PRAAx] le (rd term d (succ j) x) (inst2 p (succ j) x) :=
  le_congr (rd_succ j x).eqSymm (.eqRefl _) (mx_lub ht (le_trans (hmono j _ _ x ih) he))

theorem least_all
    (hmono : ∀ {k : ℕ} {Θ : List (Fm PTm k)} (j q q' y : PTm k),
      (Θ ⊢[PRAAx] le q q') → (Θ ⊢[PRAAx] le (dAt d j q y) (dAt d j q' y)))
    {x : PTm n} (hp0 : Γ ⊢[PRAAx] le (inst2 term zero x) (inst2 p zero x))
    (hpt : Γ ⊢[PRAAx] Fm.all (le (inst2 term (succ (var 0)) (Syn.shift x))
      (inst2 p (succ (var 0)) (Syn.shift x))))
    (hpe : Γ ⊢[PRAAx] Fm.all (le (dAt d (var 0) (inst2 p (var 0) (Syn.shift x)) (Syn.shift x))
      (inst2 p (succ (var 0)) (Syn.shift x)))) :
    Γ ⊢[PRAAx] Fm.all (le (rd term d (var 0) (Syn.shift x)) (inst2 p (var 0) (Syn.shift x))) := by
  refine PRA.qfInd _ (le_QF _ _) ?_ ?_
  · simp only [subst_le, subst_ap2, subst_inst2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact least_base hp0
  · simp only [subst_le, subst_ap2, subst_inst2, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact least_step hmono hpt.allOpen.wk hpe.allOpen.wk Prf.hyp0

/-- `lem:demand-least`, chain case: the reverse demand is below every satisfying request vector. -/
theorem least
    (hmono : ∀ {k : ℕ} {Θ : List (Fm PTm k)} (j q q' y : PTm k),
      (Θ ⊢[PRAAx] le q q') → (Θ ⊢[PRAAx] le (dAt d j q y) (dAt d j q' y)))
    {x : PTm n} (hp0 : Γ ⊢[PRAAx] le (inst2 term zero x) (inst2 p zero x))
    (hpt : Γ ⊢[PRAAx] Fm.all (le (inst2 term (succ (var 0)) (Syn.shift x))
      (inst2 p (succ (var 0)) (Syn.shift x))))
    (hpe : Γ ⊢[PRAAx] Fm.all (le (dAt d (var 0) (inst2 p (var 0) (Syn.shift x)) (Syn.shift x))
      (inst2 p (succ (var 0)) (Syn.shift x))))
    (j : PTm n) : Γ ⊢[PRAAx] le (rd term d j x) (inst2 p j x) := by
  have a := Prf.allE j (least_all hmono hp0 hpt hpe)
  simp only [subst_le, subst_ap2, subst_inst2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at a
  exact a

end Demand

end LeanProofs.IPRA.Foundations.ReverseDemand

export_ipra Foundations.ReverseDemand (le_mx_left le_mx_right mx_lub)
