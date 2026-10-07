import OAI.Combinatorics.Progressions.Estimates.AxisCompression
import OAI.Combinatorics.Progressions.Geometry.BoxCyclicEncoding

namespace OAI

section

namespace Erdos3

open scoped BigOperators

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_native_integer_box_inverse (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {n : ℕ} (T : Fin n → ℕ) [∀ i, NeZero (T i)]
      {p : ℝ}, 2 ≤ p → ∀ f : (Fin n → ℤ) → ℂ,
      (∀ x ∈ integerBox T, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ integerBoxGowersNorm T (s + 1) f →
      ∃ V : NativeSampleCorrelation (fun _ : Fin n => 1) s ((p + n + C) ^ C) (integerBox T) id f,
        V.test.normBound ≤ 1 := by
  obtain ⟨A, _, htransfer⟩ := exists_native_inverse_on_cyclic_encoding s hs
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((4 * X + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro n T _ p hp f hf hGowers
  have hp0 : 0 ≤ p := by linarith
  have hcost : (p + 4 * (n : ℝ) + A) ^ A ≤ (p + n + C) ^ C := by
    apply (pow_le_pow_left₀ (by positivity)
      (show p + 4 * (n : ℝ) + A ≤ 4 * (p + n) + A by linarith) A).trans
    simpa [X, Polynomial.eval₂_pow] using hbudget (p + n) (by positivity)
  obtain ⟨V, hV⟩ := htransfer (integerBox T) (integerBox_nonempty T) (boxIntegerCode T)
    (boxCyclicCode_reflectsPairSums T) (fun x hx => boxIntegerCode_bounds T x hx)
    hp (by positivity : (0 : ℝ) ≤ 4 * n) (boxCode_density_lower T) f hf hGowers
  exact ⟨V.mono hcost, hV⟩

theorem exists_native_integer_box_inverse_bounded_dimension (s : ℕ) (hs : 1 ≤ s) (D : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {n : ℕ} (T : Fin n → ℕ) [∀ i, NeZero (T i)]
      {p : ℝ}, 2 ≤ p → (n : ℝ) ≤ (p + D) ^ D → ∀ f : (Fin n → ℤ) → ℂ,
      (∀ x ∈ integerBox T, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ integerBoxGowersNorm T (s + 1) f →
      ∃ V : NativeSampleCorrelation (fun _ : Fin n => 1) s ((p + C) ^ C) (integerBox T) id f,
        V.test.normBound ≤ 1 := by
  obtain ⟨A, _, hinverse⟩ := exists_native_integer_box_inverse s hs
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + (X + Polynomial.C D) ^ D + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro n T _ p hp hn f hf hGowers
  have hp0 : 0 ≤ p := by linarith
  have hcost : (p + n + A) ^ A ≤ (p + C) ^ C := by
    apply (pow_le_pow_left₀ (by positivity)
      (show p + (n : ℝ) + A ≤ p + (p + D) ^ D + A by linarith) A).trans
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp0
  obtain ⟨V, hV⟩ := hinverse T hp f hf hGowers
  exact ⟨V.mono hcost, hV⟩

end Erdos3

end

end OAI
