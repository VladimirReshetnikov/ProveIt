import OAI.Combinatorics.Progressions.Polynomial.WeightedLieDegreeLengthSpan

namespace OAI

section

namespace Erdos3

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L]

def markedLieSpan (v : I → L) (w : I → ℕ) (marked : I → Bool) (d k l : ℕ) : Submodule ℚ L :=
  Submodule.span ℚ {x | ∃ a : FreeMagma I, d ≤ lieTreeWeight w a ∧
    k ≤ lieTreeMarkedCount marked a ∧ l ≤ a.length ∧ lieTreeEval v a = x}

theorem markedLieSpan_antitone (v : I → L) (w : I → ℕ) (marked : I → Bool)
    {d e k m l n : ℕ} (hde : d ≤ e) (hkm : k ≤ m) (hln : l ≤ n) :
    markedLieSpan v w marked e m n ≤ markedLieSpan v w marked d k l := by
  apply Submodule.span_mono
  rintro x ⟨a, hd, hk, hl, rfl⟩
  exact ⟨a, hde.trans hd, hkm.trans hk, hln.trans hl, rfl⟩

theorem markedLieSpan_lie_mem (v : I → L) (w : I → ℕ) (marked : I → Bool)
    {d e k m l n : ℕ} {x y : L}
    (hx : x ∈ markedLieSpan v w marked d k l)
    (hy : y ∈ markedLieSpan v w marked e m n) :
    ⁅x, y⁆ ∈ markedLieSpan v w marked (d + e) (k + m) (l + n) := by
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
    obtain ⟨a, hd, hk, hl, rfl⟩ := hx
    obtain ⟨b, he, hm, hn, rfl⟩ := hy
    exact Submodule.subset_span ⟨a * b, Nat.add_le_add hd he,
      Nat.add_le_add hk hm, Nat.add_le_add hl hn, rfl⟩
  | zero_left y _ => rw [zero_lie]; exact Submodule.zero_mem _
  | zero_right x _ => rw [lie_zero]; exact Submodule.zero_mem _
  | add_left x y z _ _ _ hx hy => rw [add_lie]; exact Submodule.add_mem _ hx hy
  | add_right x y z _ _ _ hx hy => rw [lie_add]; exact Submodule.add_mem _ hx hy
  | smul_left c x y _ _ h => rw [smul_lie]; exact Submodule.smul_mem _ c h
  | smul_right c x y _ _ h => rw [lie_smul]; exact Submodule.smul_mem _ c h

theorem markedLieSpan_leaf (v : I → L) (w : I → ℕ) (marked : I → Bool) (i : I) :
    v i ∈ markedLieSpan v w marked (w i) (if marked i then 1 else 0) 1 :=
  Submodule.subset_span ⟨.of i, le_rfl, le_rfl, le_rfl, rfl⟩

theorem markedLieSpan_zero_marked (v : I → L) (w : I → ℕ) (marked : I → Bool) (d l : ℕ) :
    markedLieSpan v w marked d 0 l = weightedLieDegreeLengthSpan v w d l := by
  unfold markedLieSpan weightedLieDegreeLengthSpan
  congr 1
  ext x
  simp only [Nat.zero_le, true_and]

theorem markedLieSpan_le_layer {s r : ℕ} (F : DegreeRankLieFiltration L s r)
    (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (hv : ∀ i, v i ∈ F.layer (w i) 1) (d k l : ℕ) :
    markedLieSpan v w marked d k l ≤ F.layer d l := by
  apply Submodule.span_le.mpr
  rintro x ⟨a, hd, _, hl, rfl⟩
  exact F.degree_antitone l hd
    (F.rank_antitone (lieTreeWeight w a) hl (F.lieTreeEval_mem_length v w hv a))

theorem markedLieSpan_top_le_ker {A : Type*} [AddCommGroup A] [Module ℚ A]
    {s r : ℕ} (F : DegreeRankLieFiltration L s r)
    (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (hv : ∀ i, v i ∈ F.layer (w i) 1) (k : ℕ) (η : L →ₗ[ℚ] A)
    (hzero : ∀ a : FreeMagma I, lieTreeWeight w a = s → a.length = r →
      k ≤ lieTreeMarkedCount marked a → η (lieTreeEval v a) = 0) :
    markedLieSpan v w marked s k r ≤ η.ker := by
  apply Submodule.span_le.mpr
  rintro x ⟨a, hd, hk, hl, rfl⟩
  change η (lieTreeEval v a) = 0
  by_cases he : lieTreeWeight w a = s
  · by_cases hn : a.length = r
    · exact hzero a he hn hk
    · have hm := F.lieTreeEval_mem_length v w hv a
      rw [F.layer_eq_bot_of_past_top (Or.inr ⟨he.symm, by omega⟩), Submodule.mem_bot] at hm
      rw [hm, map_zero]
  · have hm := F.lieTreeEval_mem_length v w hv a
    rw [F.layer_eq_bot_of_past_top (Or.inl (by omega)), Submodule.mem_bot] at hm
    rw [hm, map_zero]

theorem markedLieSpan_marked_terminal {s r : ℕ} (F : DegreeRankLieFiltration L s r)
    (v : I → L) (w : I → ℕ) (marked : I → Bool) (hw : ∀ i, 0 < w i)
    (hv : ∀ i, v i ∈ F.layer (w i) 1) (d l : ℕ) :
    markedLieSpan v w marked d (s + 1) l = ⊥ := by
  apply bot_unique
  apply Submodule.span_le.mpr
  rintro x ⟨a, _, hk, _, rfl⟩
  have hcount := (lieTreeMarkedCount_le_length marked a).trans (lieTree_length_le_weight w hw a)
  have hs : s < lieTreeWeight w a := by omega
  have hm := F.lieTreeEval_mem_length v w hv a
  rw [F.layer_eq_bot_of_past_top (Or.inl hs)] at hm
  exact hm

end Erdos3

end

end OAI
