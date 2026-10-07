import OAI.Combinatorics.Progressions.Estimates.PhysicalCubeNativeDetection

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_large_vertex_of_cube_mixture
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Fintype B] [DecidableEq B]
    {φ : A →+ B} {Q : Finset A} (hφ : ReflectsPairSums φ (Q : Set A))
    (s : ℕ) {I : Type*} [Fintype I] (p : ℝ)
    (c : I → ℂ) (F : I → (Fin (s + 1) → Bool) → A → ℂ)
    (hF : ∀ i ω x, x ∈ Q → ‖F i ω x‖ ≤ 1)
    (hc : (∑ i, ‖c i‖) ≤ Real.exp p)
    (z : ℂ) (hz : Real.exp (-p) ≤ z.re)
    (herr : ‖z - ∑ i, c i * normalizedSupportedCubeSum (s + 1) Q (F i)‖ ≤ Real.exp (-p) / 2)
    (ω : Fin (s + 1) → Bool) :
    ∃ i, Real.exp (-(2 * p + 2)) ≤ finiteSupportGowersNorm (s + 1) Q (F i ω) := by
  have hlarge : Real.exp (-p) / 2 ≤
      ‖∑ i, c i * normalizedSupportedCubeSum (s + 1) Q (F i)‖ := by
    have h := norm_sub_norm_le z (∑ i, c i * normalizedSupportedCubeSum (s + 1) Q (F i))
    have hreal := Complex.re_le_norm z
    linarith
  obtain ⟨i, hi⟩ := exists_large_weighted_term c
    (fun i => normalizedSupportedCubeSum (s + 1) Q (F i))
    (half_pos (Real.exp_pos _)) (Real.exp_pos p) hc hlarge
  have he : Real.exp (-(2 * p)) / 2 = (Real.exp (-p) / 2) / Real.exp p := by
    rw [div_right_comm, ← Real.exp_sub]
    congr 2
    ring
  have hsmall : Real.exp (-(2 * p + 2)) ≤ Real.exp (-(2 * p)) / 2 :=
    (Real.exp_le_exp.mpr (by linarith : -(2 * p + 2) ≤ -(2 * p) - 1)).trans
      (exp_sub_one_le_half_exp (-(2 * p)))
  rw [he] at hsmall
  exact ⟨i, (hsmall.trans hi).trans (normalizedSupportedCubeSum_le_vertex hφ s (F i) (hF i) ω)⟩

theorem exists_site_twist_of_degree_zero_cube_mixture
    {X : Type*} [Fintype X] [DecidableEq X] (N : X → ℕ) [∀ x, NeZero (N x)]
    {I : Type*} [Fintype I] (p : ℝ) (f : (X → ℤ) → ℂ) (c : I → ℂ)
    (twist : I → Finset (Fin 1) → (X → ℤ) → ℂ)
    (hf : ∀ x ∈ integerBox N, ‖f x‖ ≤ 1)
    (ht : ∀ i ω x, x ∈ integerBox N → ‖twist i ω x‖ ≤ 1)
    (hc : (∑ i, ‖c i‖) ≤ Real.exp p) (z : ℂ) (hz : Real.exp (-p) ≤ z.re)
    (herr : ‖z - ∑ i, c i *
      (𝔼 cube : SupportedCube 1 (integerBox N : Set (X → ℤ)),
        let u := (BooleanCubeKernel.physicalCubeParametersEquiv X 1).symm cube.val
        ∏ ω, conjugationPower ω.card (f (BooleanCubeKernel.physicalCubeVertexValue u ω)) *
          twist i ω (BooleanCubeKernel.physicalCubeVertexValue u ω))‖ ≤ Real.exp (-p) / 2) :
    ∃ i, Real.exp (-(2 * p + 2)) ≤ ‖𝔼 x ∈ integerBox N, f x * twist i ∅ x‖ := by
  let F : I → (Fin 1 → Bool) → (X → ℤ) → ℂ := fun i ω x =>
    f x * conjugationPower (booleanWeight ω)
      (twist i (BooleanCubeKernel.vertexFinsetEquiv 1 ω) x)
  have hF : ∀ i ω x, x ∈ integerBox N → ‖F i ω x‖ ≤ 1 := by
    intro i ω x hx
    dsimp only [F]
    rw [norm_mul, conjugationPower_norm]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hf x hx)).trans (ht i _ x hx)
  simp_rw [BooleanCubeKernel.physical_twisted_cube_mean] at herr
  obtain ⟨i, hi⟩ := exists_large_vertex_of_cube_mixture (boxReduction_reflectsPairSums N)
    0 p c F hF hc z hz herr (fun _ => false)
  rw [finiteSupportGowersNorm_degree_one_of_embedding
    (boxReduction_reflectsPairSums N) (integerBox_nonempty N)] at hi
  refine ⟨i, ?_⟩
  simpa only [F, booleanWeight, Bool.false_eq_true, ↓reduceIte, Finset.sum_const_zero,
    conjugationPower, RingHom.id_apply, BooleanCubeKernel.vertexFinsetEquiv,
    Equiv.coe_fn_mk, Finset.filter_false] using hi

end Erdos3

end

end OAI
