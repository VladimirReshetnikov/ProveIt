import OAI.Combinatorics.Progressions.Lattices.NativeIntegerAffinePullbackHom

namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

theorem exists_large_nonnegative_weighted_term {I : Type*} [Fintype I]
    (w z : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hz : ∀ i, 0 ≤ z i)
    {ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 < M)
    (hcost : ∑ i, w i ≤ M) (hmass : ρ ≤ ∑ i, w i * z i) :
    ∃ i, ρ / M ≤ z i := by
  classical
  have hI : (Finset.univ : Finset I).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hmass
    linarith
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ z hI
  refine ⟨i, (div_le_iff₀ hM).mpr ?_⟩
  calc
    ρ ≤ ∑ j, w j * z j := hmass
    _ ≤ ∑ j, w j * z i := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hi j (Finset.mem_univ j)) (hw j))
    _ = (∑ j, w j) * z i := (Finset.sum_mul _ _ _).symm
    _ ≤ M * z i := mul_le_mul_of_nonneg_right hcost (hz i)
    _ = z i * M := mul_comm _ _

theorem mean_row_weighted_sum_norm_le {H X I : Type*} [Fintype H] [Fintype X] [Fintype I]
    (c : I → ℂ) (F : I → H → X → ℂ) :
    (𝔼 h, ‖𝔼 x, ∑ i, c i * F i h x‖) ≤ ∑ i, ‖c i‖ * (𝔼 h, ‖𝔼 x, F i h x‖) := by
  have hp (h : H) : ‖𝔼 x, ∑ i, c i * F i h x‖ ≤ ∑ i, ‖c i‖ * ‖𝔼 x, F i h x‖ := by
    simp_rw [Finset.expect_sum_comm, ← Finset.mul_expect]
    exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul])
  have hm := Finset.expect_le_expect (s := Finset.univ) (fun h _ => hp h)
  simpa only [Finset.expect_sum_comm, ← Finset.mul_expect] using hm

theorem exists_mean_row_weighted_term {H X I : Type*} [Fintype H] [Fintype X] [Fintype I]
    (c : I → ℂ) (F : I → H → X → ℂ) {ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 < M)
    (hcost : ∑ i, ‖c i‖ ≤ M) (hmass : ρ ≤ 𝔼 h, ‖𝔼 x, ∑ i, c i * F i h x‖) :
    ∃ i, ρ / M ≤ 𝔼 h, ‖𝔼 x, F i h x‖ :=
  exists_large_nonnegative_weighted_term (fun i => ‖c i‖) (fun i => 𝔼 h, ‖𝔼 x, F i h x‖)
    (fun _ => norm_nonneg _) (fun _ => Finset.expect_nonneg (fun _ _ => norm_nonneg _))
    hρ hM hcost (hmass.trans (mean_row_weighted_sum_norm_le c F))

namespace NativeIntegerExpansion

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem select_mean_row_correlation {σ H X : Type*} [Fintype H] [Fintype X]
    {w : σ → ℕ} {s : ℕ} {p : ℝ} {g : (σ → ℤ) → ℂ}
    (E : NativeIntegerExpansion w s p g) (sample : H → X → σ → ℤ) (f : H → X → ℂ)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hmass : ρ ≤ 𝔼 h, ‖𝔼 x, f h x * star (g (sample h x))‖) :
    ∃ i : Fin E.count, ρ / Real.exp p ≤
      𝔼 h, ‖𝔼 x, f h x * star ((E.test i).eval (sample h x))‖ := by
  let F (i : Fin E.count) (h : H) (x : X) := f h x * star ((E.test i).eval (sample h x))
  have heq (h : H) (x : X) : f h x * star (g (sample h x)) =
      ∑ i, star (E.coefficient i) * F i h x := by
    rw [E.eval, star_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [F, star_mul]
    ring
  simp only [heq] at hmass
  exact exists_mean_row_weighted_term (fun i => star (E.coefficient i)) F hρ (Real.exp_pos _)
    (by simpa only [norm_star] using E.cost) hmass

end NativeIntegerExpansion
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem mean_row_correlation_scale {H X : Type*} [Fintype H] [Fintype X]
    (f g : H → X → ℂ) {a : ℝ} (ha : 0 ≤ a) :
    (𝔼 h, ‖𝔼 x, f h x * star ((a : ℂ) * g h x)‖) =
      a * (𝔼 h, ‖𝔼 x, f h x * star (g h x)‖) := by
  have heq (h : H) : (𝔼 x, f h x * star ((a : ℂ) * g h x)) =
      (a : ℂ) * (𝔼 x, f h x * star (g h x)) := by
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro x _
    simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  simp only [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha,
    ← Finset.mul_expect]

theorem exists_large_value_of_mean_row_correlation {H X : Type*}
    [Fintype H] [Nonempty H] [Fintype X] [Nonempty X]
    (f g : H → X → ℂ) (hf : ∀ h x, ‖f h x‖ ≤ 1) {ρ : ℝ}
    (hcorr : ρ ≤ 𝔼 h, ‖𝔼 x, f h x * star (g h x)‖) :
    ∃ h x, ρ ≤ ‖g h x‖ := by
  have hb : ρ ≤ 𝔼 h, 𝔼 x, ‖g h x‖ := by
    apply hcorr.trans
    apply Finset.expect_le_expect
    intro h _
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply Finset.expect_le_expect
    intro x _
    rw [norm_mul, norm_star]
    exact mul_le_of_le_one_left (norm_nonneg _) (hf h x)
  obtain ⟨h, _, hh⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hb
  obtain ⟨x, _, hx⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hh
  exact ⟨h, x, hx⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeMeanRowCorrelation {σ H X : Type*} [Fintype H] [Fintype X]
    (w : σ → ℕ) (degree : ℕ) (p : ℝ) (sample : H → X → σ → ℤ) (f : H → X → ℂ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L degree dim
  test : model.Niltest w
  complexity : test.ComplexityLE p
  correlation : Real.exp (-p) ≤ 𝔼 h, ‖𝔼 x, f h x * star (test.eval (sample h x))‖

attribute [local instance] NativeMeanRowCorrelation.lie NativeMeanRowCorrelation.algebra
  NativeMeanRowCorrelation.topology NativeMeanRowCorrelation.topologicalAdd
  NativeMeanRowCorrelation.continuousSMul NativeMeanRowCorrelation.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeMeanRowCorrelation

variable {σ H X : Type*} [Fintype H] [Fintype X] {w : σ → ℕ} {s : ℕ} {p q : ℝ}
  {sample : H → X → σ → ℤ} {f : H → X → ℂ}

noncomputable def mono (V : NativeMeanRowCorrelation w s p sample f) (hpq : p ≤ q) :
    NativeMeanRowCorrelation w s q sample f :=
  { V with
    complexity := V.complexity.mono hpq
    correlation := (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans V.correlation }

theorem exists_of_expansion {g : (σ → ℤ) → ℂ}
    (E : NativeIntegerExpansion w s p g) (hq : 0 ≤ q)
    (hcorr : Real.exp (-q) ≤ 𝔼 h, ‖𝔼 x, f h x * star (g (sample h x))‖) :
    Nonempty (NativeMeanRowCorrelation w s (q + p) sample f) := by
  obtain ⟨i, hi⟩ := E.select_mean_row_correlation sample f (Real.exp_pos _) hcorr
  refine ⟨{
    L := E.L i
    dim := E.dim i
    model := E.model i
    test := E.test i
    complexity := (E.complexity i).mono (le_add_of_nonneg_left hq)
    correlation := ?_ }⟩
  have heq : Real.exp (-q) / Real.exp p = Real.exp (-(q + p)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rwa [heq] at hi

end NativeMeanRowCorrelation
end Erdos3

end

end OAI
