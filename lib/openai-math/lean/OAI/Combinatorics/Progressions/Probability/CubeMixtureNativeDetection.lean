import OAI.Combinatorics.Progressions.Geometry.SupportedCubeUnitBounds
import OAI.Combinatorics.Progressions.Lattices.NativeIntegerBoxInverse

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_native_partner_of_cube_mixture (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {n : ℕ} (N : Fin n → ℕ) [∀ i, NeZero (N i)]
      {I : Type*} [Fintype I] (p : ℝ), 0 ≤ p → (n : ℝ) ≤ p →
      ∀ (f : (Fin n → ℤ) → ℂ) (c : I → ℂ)
        (twist : I → (Fin (s + 1) → Bool) → (Fin n → ℤ) → ℂ),
      (∀ x ∈ integerBox N, ‖f x‖ ≤ 1) →
      (∀ i ω x, x ∈ integerBox N → ‖twist i ω x‖ ≤ 1) →
      (∑ i, ‖c i‖) ≤ Real.exp p →
      ∀ z : ℂ, Real.exp (-p) ≤ z.re →
      ‖z - ∑ i, c i * normalizedSupportedCubeSum (s + 1) (integerBox N)
        (fun ω x => f x * twist i ω x)‖ ≤ Real.exp (-p) / 2 →
      ∀ ω : Fin (s + 1) → Bool,
      ∃ (i : I) (V : NativeSampleCorrelation (fun _ : Fin n => 1) s ((p + 2) ^ C)
        (integerBox N) id (fun x => f x * twist i ω x)),
        V.test.normBound ≤ 1 ∧
        Real.exp (-((p + 2) ^ C)) ≤
          ‖𝔼 x ∈ integerBox N, f x * star (star (twist i ω x) * V.test.eval x)‖ := by
  obtain ⟨A, _, hinverse⟩ := exists_native_integer_box_inverse s hs
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget ((3 * X + 2 + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro n N _ I _ p hp hn f c twist hf htwist hc z hz herr ω
  let F := fun i ω x => f x * twist i ω x
  have hF (i) (ω) (x) (hx : x ∈ integerBox N) : ‖F i ω x‖ ≤ 1 := by
    dsimp only [F]
    rw [norm_mul]
    exact (mul_le_mul (hf x hx) (htwist i ω x hx) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hlarge : Real.exp (-p) / 2 ≤
      ‖∑ i, c i * normalizedSupportedCubeSum (s + 1) (integerBox N) (F i)‖ := by
    have h := norm_sub_norm_le z (∑ i, c i * normalizedSupportedCubeSum (s + 1) (integerBox N) (F i))
    have hreal := Complex.re_le_norm z
    linarith
  obtain ⟨i, hi⟩ := exists_large_weighted_term c
    (fun i => normalizedSupportedCubeSum (s + 1) (integerBox N) (F i))
    (half_pos (Real.exp_pos _)) (Real.exp_pos p) hc hlarge
  have hG : Real.exp (-(2 * p + 2)) ≤ integerBoxGowersNorm N (s + 1) (F i ω) := by
    have he : Real.exp (-(2 * p)) / 2 = (Real.exp (-p) / 2) / Real.exp p := by
      rw [div_right_comm, ← Real.exp_sub]
      congr 2
      ring
    have hsmall : Real.exp (-(2 * p + 2)) ≤ Real.exp (-(2 * p)) / 2 :=
      (Real.exp_le_exp.mpr (by linarith : -(2 * p + 2) ≤ -(2 * p) - 1)).trans
        (exp_sub_one_le_half_exp (-(2 * p)))
    rw [he] at hsmall
    exact (hsmall.trans hi).trans
      (normalizedSupportedCubeSum_le_vertex (boxReduction_reflectsPairSums N) s (F i) (hF i) ω)
  obtain ⟨V, hV⟩ := hinverse N (by linarith : 2 ≤ 2 * p + 2) (F i ω) (hF i ω) hG
  have hcost : (2 * p + 2 + n + A) ^ A ≤ (p + 2) ^ C := by
    apply (pow_le_pow_left₀ (by positivity)
      (show 2 * p + 2 + (n : ℝ) + A ≤ 3 * p + 2 + A by linarith) A).trans
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨i, V.mono hcost, hV, ?_⟩
  simpa only [star_mul, star_star, F, id_eq, mul_assoc, mul_left_comm, mul_comm] using
    (V.mono hcost).correlation

end Erdos3

end

end OAI
