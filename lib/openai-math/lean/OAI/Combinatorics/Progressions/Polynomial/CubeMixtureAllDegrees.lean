import OAI.Combinatorics.Progressions.Probability.CubeMixtureVertex

namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_native_partner_of_physical_cube_mixture_all_degrees (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {n : ℕ} (N : Fin n → ℕ) [∀ i, NeZero (N i)]
      {I : Type*} [Fintype I] (p : ℝ), 0 ≤ p → (n : ℝ) ≤ p →
      ∀ (f : (Fin n → ℤ) → ℂ) (c : I → ℂ)
        (twist : I → Finset (Fin (s + 1)) → (Fin n → ℤ) → ℂ),
      (∀ x ∈ integerBox N, ‖f x‖ ≤ 1) →
      (∀ i ω x, x ∈ integerBox N → ‖twist i ω x‖ ≤ 1) →
      (∑ i, ‖c i‖) ≤ Real.exp p →
      ∀ z : ℂ, Real.exp (-p) ≤ z.re →
      ‖z - ∑ i, c i * (𝔼 cube : SupportedCube (s + 1) (integerBox N : Set ((Fin n) → ℤ)),
        let u := (physicalCubeParametersEquiv (Fin n) (s + 1)).symm cube.val
        ∏ ω, conjugationPower ω.card (f (physicalCubeVertexValue u ω)) *
          twist i ω (physicalCubeVertexValue u ω))‖ ≤ Real.exp (-p) / 2 →
      ∃ (i : I) (V : NativeSampleCorrelation (fun _ : Fin n => 1) s ((p + 2) ^ C)
        (integerBox N) id (fun x => f x * twist i ∅ x)),
        V.test.normBound ≤ 1 ∧
        Real.exp (-((p + 2) ^ C)) ≤
          ‖𝔼 x ∈ integerBox N, f x * star (star (twist i ∅ x) * V.test.eval x)‖ := by
  by_cases hs : s = 0
  · subst s
    refine ⟨2, le_rfl, ?_⟩
    intro n N _ I _ p hp hn f c twist hf ht hc z hz herr
    obtain ⟨i, hi⟩ := exists_site_twist_of_degree_zero_cube_mixture (X := Fin n)
      (I := I) N p f c twist hf ht hc z hz herr
    have hcost : 2 * p + 2 ≤ (p + 2) ^ 2 := by nlinarith [sq_nonneg p]
    have hlow : 2 ≤ (p + 2) ^ 2 := by nlinarith [sq_nonneg p]
    let V : NativeSampleCorrelation (fun _ : Fin n => 1) 0 ((p + 2) ^ 2)
        (integerBox N) id (fun x => f x * twist i ∅ x) :=
      NativeSampleCorrelation.ofMean hlow ((Real.exp_le_exp.mpr (neg_le_neg hcost)).trans hi)
    refine ⟨i, V, ?_, ?_⟩
    · simp only [V, NativeSampleCorrelation.ofMean, RationalFilteredNilmanifold.Niltest.const,
        nnnorm_one, le_refl]
    · simpa only [star_mul, star_star, id_eq, mul_assoc, mul_left_comm, mul_comm] using V.correlation
  · exact exists_native_partner_of_physical_cube_mixture s (Nat.one_le_iff_ne_zero.mpr hs)

end Erdos3

end

end OAI
