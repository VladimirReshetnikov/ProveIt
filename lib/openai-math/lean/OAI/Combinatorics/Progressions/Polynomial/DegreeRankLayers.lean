import OAI.Combinatorics.Progressions.Estimates.FilteredLieTree

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def rankGenerators (d r : ℕ) : Set L :=
  {x | ∃ k, r ≤ k ∧ ∃ a : FilteredLieTree F d k, a.eval = x}

def rankLayer (d r : ℕ) : Submodule ℚ L :=
  F.layer (d + 1) ⊔ Submodule.span ℚ (F.rankGenerators d r)

theorem layer_succ_le_rankLayer (d r : ℕ) : F.layer (d + 1) ≤ F.rankLayer d r := le_sup_left

theorem span_rankGenerators_le_rankLayer (d r : ℕ) :
    Submodule.span ℚ (F.rankGenerators d r) ≤ F.rankLayer d r := le_sup_right

theorem tree_eval_mem_rankLayer {d r k : ℕ} (a : FilteredLieTree F d k) (hr : r ≤ k) :
    a.eval ∈ F.rankLayer d r :=
  F.span_rankGenerators_le_rankLayer d r (Submodule.subset_span ⟨k, hr, a, rfl⟩)

theorem rankLayer_le_layer (d r : ℕ) : F.rankLayer d r ≤ F.layer d := by
  apply sup_le (F.antitone (by omega))
  apply Submodule.span_le.mpr
  rintro x ⟨k, _, a, rfl⟩
  exact a.eval_mem

theorem rankLayer_rank_antitone (d : ℕ) : Antitone (F.rankLayer d) := by
  intro r t hrt
  apply sup_le_sup_left
  apply Submodule.span_mono
  rintro x ⟨k, htk, a, hx⟩
  exact ⟨k, hrt.trans htk, a, hx⟩

theorem rankLayer_degree_le {d e : ℕ} (hde : d < e) (r t : ℕ) :
    F.rankLayer e t ≤ F.rankLayer d r :=
  (F.rankLayer_le_layer e t).trans
    ((F.antitone (show d + 1 ≤ e by omega)).trans (F.layer_succ_le_rankLayer d r))

theorem rankLayer_lex_antitone {d e r t : ℕ} (h : d < e ∨ d = e ∧ r ≤ t) :
    F.rankLayer e t ≤ F.rankLayer d r := by
  rcases h with h | ⟨rfl, h⟩
  · exact F.rankLayer_degree_le h r t
  · exact F.rankLayer_rank_antitone d h

theorem rankLayer_eq_layer_of_rank_le_one (d : ℕ) {r : ℕ} (hr : r ≤ 1) :
    F.rankLayer d r = F.layer d := by
  apply le_antisymm (F.rankLayer_le_layer d r)
  intro x hx
  by_cases hd : d = 0
  · subst d
    exact F.layer_succ_le_rankLayer 0 r (by simp only [zero_add, F.one_eq_top, Submodule.mem_top])
  · exact F.tree_eval_mem_rankLayer (.leaf (by omega) x hx) hr

theorem rankLayer_zero (d : ℕ) : F.rankLayer d 0 = F.layer d :=
  F.rankLayer_eq_layer_of_rank_le_one d (by omega)

theorem rankLayer_one (d : ℕ) : F.rankLayer d 1 = F.layer d :=
  F.rankLayer_eq_layer_of_rank_le_one d le_rfl

theorem rankLayer_eq_next_of_degree_lt_rank {d r : ℕ} (hdr : d < r) :
    F.rankLayer d r = F.layer (d + 1) := by
  have hgen : F.rankGenerators d r = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨k, hrk, a, _⟩
    have := a.rank_le_degree
    omega
  simp only [rankLayer, hgen, Submodule.span_empty, sup_bot_eq]

theorem rankLayer_eq_bot_of_degree_gt {d : ℕ} (hd : s < d) (r : ℕ) :
    F.rankLayer d r = ⊥ := by
  apply bot_unique
  exact (F.rankLayer_le_layer d r).trans
    ((F.antitone (show s + 1 ≤ d by omega)).trans F.terminal.le)

theorem rankLayer_top_terminal (r : ℕ) (hr : s < r) : F.rankLayer s r = ⊥ := by
  rw [F.rankLayer_eq_next_of_degree_lt_rank hr, F.terminal]

end Erdos3.NilpotentLieFiltration

end

end OAI
