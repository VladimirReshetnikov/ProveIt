import OAI.Combinatorics.Progressions.Linear.WeightedLieUpperSpan
import OAI.Combinatorics.Progressions.Polynomial.DegreeRankSunflower

namespace OAI

section

namespace Erdos3

variable {I L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

def weightedLieDegreeLengthSpan (v : I → L) (w : I → ℕ) (d k : ℕ) : Submodule ℚ L :=
  Submodule.span ℚ {x | ∃ a : FreeMagma I, d ≤ lieTreeWeight w a ∧ k ≤ a.length ∧ lieTreeEval v a = x}

theorem weightedLieDegreeLengthSpan_antitone (v : I → L) (w : I → ℕ)
    {d e k l : ℕ} (hde : d ≤ e) (hkl : k ≤ l) :
    weightedLieDegreeLengthSpan v w e l ≤ weightedLieDegreeLengthSpan v w d k := by
  apply Submodule.span_mono
  rintro x ⟨a, ha, hk, rfl⟩
  exact ⟨a, hde.trans ha, hkl.trans hk, rfl⟩

theorem weightedLieDegreeLengthSpan_lie_mem (v : I → L) (w : I → ℕ)
    {d e k l : ℕ} {x y : L}
    (hx : x ∈ weightedLieDegreeLengthSpan v w d k)
    (hy : y ∈ weightedLieDegreeLengthSpan v w e l) :
    ⁅x, y⁆ ∈ weightedLieDegreeLengthSpan v w (d + e) (k + l) := by
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
    obtain ⟨a, ha, hk, rfl⟩ := hx
    obtain ⟨b, hb, hl, rfl⟩ := hy
    exact Submodule.subset_span ⟨a * b, Nat.add_le_add ha hb, Nat.add_le_add hk hl, rfl⟩
  | zero_left y _ => rw [zero_lie]; exact Submodule.zero_mem _
  | zero_right x _ => rw [lie_zero]; exact Submodule.zero_mem _
  | add_left x y z _ _ _ hx hy => rw [add_lie]; exact Submodule.add_mem _ hx hy
  | add_right x y z _ _ _ hx hy => rw [lie_add]; exact Submodule.add_mem _ hx hy
  | smul_left c x y _ _ h => rw [smul_lie]; exact Submodule.smul_mem _ c h
  | smul_right c x y _ _ h => rw [lie_smul]; exact Submodule.smul_mem _ c h

theorem weightedLieUpperSpan_map_le_degreeLengthSpan (φ : L →ₗ⁅ℚ⁆ M)
    (v : I → L) (w : I → ℕ) (d : ℕ) :
    (weightedLieUpperSpan v w d).map φ.toLinearMap ≤
      weightedLieDegreeLengthSpan (fun i => φ (v i)) w d 1 := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro x ⟨a, ha, rfl⟩
  change φ (lieTreeEval v a) ∈ weightedLieDegreeLengthSpan (fun i => φ (v i)) w d 1
  rw [map_lieTreeEval]
  exact Submodule.subset_span ⟨a, ha, a.length_pos, rfl⟩

theorem FilteredLieTree.map_eval_mem_degreeLengthSpan {s : ℕ}
    {F : NilpotentLieFiltration L s} (φ : L →ₗ⁅ℚ⁆ M) (v : I → M) (w : I → ℕ)
    (hspan : ∀ d, 0 < d → ∀ x ∈ F.layer d, φ x ∈ weightedLieDegreeLengthSpan v w d 1)
    {d k : ℕ} (a : FilteredLieTree F d k) :
    φ a.eval ∈ weightedLieDegreeLengthSpan v w d k := by
  induction a with
  | leaf hd x hx => exact hspan _ hd x hx
  | bracket a b ha hb =>
    rw [FilteredLieTree.eval_bracket, φ.map_lie]
    exact weightedLieDegreeLengthSpan_lie_mem v w ha hb

theorem weightedLieDegreeLengthSpan_top_le_ker {A : Type*} [AddCommGroup A] [Module ℚ A]
    {s r : ℕ} (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ)
    (hv : ∀ i, v i ∈ F.layer (w i) 1) (η : L →ₗ[ℚ] A)
    (hzero : ∀ a : FreeMagma I, lieTreeWeight w a = s → a.length = r → η (lieTreeEval v a) = 0) :
    weightedLieDegreeLengthSpan v w s r ≤ η.ker := by
  apply Submodule.span_le.mpr
  rintro x ⟨a, ha, hk, rfl⟩
  change η (lieTreeEval v a) = 0
  by_cases hd : lieTreeWeight w a = s
  · by_cases hr : a.length = r
    · exact hzero a hd hr
    · have hm := F.lieTreeEval_mem_length v w hv a
      rw [F.layer_eq_bot_of_past_top (Or.inr ⟨hd.symm, by omega⟩), Submodule.mem_bot] at hm
      rw [hm, map_zero]
  · have hm := F.lieTreeEval_mem_length v w hv a
    rw [F.layer_eq_bot_of_past_top (Or.inl (by omega)), Submodule.mem_bot] at hm
    rw [hm, map_zero]

end Erdos3

end

end OAI
