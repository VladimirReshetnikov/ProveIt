import OAI.Combinatorics.Progressions.Estimates.LieTreeMultidegree

namespace OAI

section

namespace Erdos3

variable {I L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

def weightedLieUpperGenerators (v : I → L) (w : I → ℕ) (d : ℕ) : Set L :=
  {x | ∃ a : FreeMagma I, d ≤ lieTreeWeight w a ∧ lieTreeEval v a = x}

def weightedLieUpperSpan (v : I → L) (w : I → ℕ) (d : ℕ) : Submodule ℚ L :=
  Submodule.span ℚ (weightedLieUpperGenerators v w d)

theorem weightedLieUpperSpan_antitone (v : I → L) (w : I → ℕ) :
    Antitone (weightedLieUpperSpan v w) := by
  intro d e hde
  apply Submodule.span_mono
  rintro x ⟨a, ha, rfl⟩
  exact ⟨a, hde.trans ha, rfl⟩

theorem weightedLieUpperSpan_lie_mem (v : I → L) (w : I → ℕ) {d e : ℕ} {x y : L}
    (hx : x ∈ weightedLieUpperSpan v w d) (hy : y ∈ weightedLieUpperSpan v w e) :
    ⁅x, y⁆ ∈ weightedLieUpperSpan v w (d + e) := by
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact Submodule.subset_span ⟨a * b, Nat.add_le_add ha hb, rfl⟩
  | zero_left y _ => rw [zero_lie]; exact Submodule.zero_mem _
  | zero_right x _ => rw [lie_zero]; exact Submodule.zero_mem _
  | add_left x y z _ _ _ hx hy => rw [add_lie]; exact Submodule.add_mem _ hx hy
  | add_right x y z _ _ _ hx hy => rw [lie_add]; exact Submodule.add_mem _ hx hy
  | smul_left c x y _ _ h => rw [smul_lie]; exact Submodule.smul_mem _ c h
  | smul_right c x y _ _ h => rw [lie_smul]; exact Submodule.smul_mem _ c h

theorem weightedLieUpperSpan_leaf (v : I → L) (w : I → ℕ) (i : I) :
    v i ∈ weightedLieUpperSpan v w (w i) :=
  Submodule.subset_span ⟨.of i, le_rfl, rfl⟩

theorem weightedLieTree_eval_mem_layer {s : ℕ} (F : NilpotentLieFiltration M s)
    (v : I → M) (w : I → ℕ) (hv : ∀ i, v i ∈ F.layer (w i)) (a : FreeMagma I) :
    lieTreeEval v a ∈ F.layer (lieTreeWeight w a) := by
  induction a using FreeMagma.rec with
  | of i => exact hv i
  | mul a b ha hb => exact F.lie_mem ha hb

theorem weightedLieUpperSpan_le_comap {s : ℕ} (F : NilpotentLieFiltration M s)
    (φ : L →ₗ⁅ℚ⁆ M) (v : I → L) (w : I → ℕ)
    (hv : ∀ i, φ (v i) ∈ F.layer (w i)) (d : ℕ) :
    weightedLieUpperSpan v w d ≤ (F.layer d).comap φ.toLinearMap := by
  apply Submodule.span_le.mpr
  rintro x ⟨a, ha, rfl⟩
  change φ (lieTreeEval v a) ∈ F.layer d
  rw [map_lieTreeEval]
  exact F.antitone ha (weightedLieTree_eval_mem_layer F (fun i => φ (v i)) w hv a)

end Erdos3

end

end OAI
