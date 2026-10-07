/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.HigherResidualRowDifferences

namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeMeanRowCorrelation.lie NativeMeanRowCorrelation.algebra
  NativeMeanRowCorrelation.topology NativeMeanRowCorrelation.topologicalAdd
  NativeMeanRowCorrelation.continuousSMul NativeMeanRowCorrelation.hausdorff

theorem exists_fourier_of_stepOne_cross_family :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I : Type*} [Fintype I] [Nonempty I] {N : ℕ} [NeZero N]
      {p : ℝ}, 0 ≤ p → ∀ (a b : I → ZMod N → ℂ) (K : I → (Fin 2 → ℤ) → ℂ),
      (∀ i n, ‖a i n‖ ≤ 1) → (∀ i n, ‖b i n‖ ≤ 1) →
      (∀ i, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 p (K i))) →
      Real.exp (-p) ≤ (𝔼 i, 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
        (a i n * star (b i (n + h))) * star (K i ![(h.val : ℤ), (n.val : ℤ)])‖) →
      ∃ χ : I → AddChar (ZMod N) ℂ,
        Real.exp (-((p + C) ^ C)) ≤ 𝔼 i, ‖finiteFourierCoeff (b i) (χ i)‖ := by
  obtain ⟨A, _, hfourier⟩ := exists_fourier_of_stepOne_cross_correlation
  let X : Polynomial ℕ := Polynomial.X
  let T := 3 * X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (T + (T + X + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro I _ _ N _ p hp a b K ha hb hK hcorr
  classical
  let c (i : I) := 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
    (a i n * star (b i (n + h))) * star (K i ![(h.val : ℤ), (n.val : ℤ)])‖
  let z (i : I) := Real.exp (-(2 * p)) * c i
  let t := 3 * p + 2
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hc0 (i : I) : 0 ≤ c i := Finset.expect_nonneg (fun _ _ => norm_nonneg _)
  have hcap (i : I) : c i ≤ Real.exp (2 * p) := by
    apply Finset.expect_le Finset.univ_nonempty
    intro h _
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply Finset.expect_le Finset.univ_nonempty
    intro n _
    rw [norm_mul, norm_star]
    apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans
      ((Classical.choice (hK i)).norm_eval_le _)
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (ha i n)).trans (hb i (n + h))
  have hzcap (i : I) : z i ≤ 1 := by
    calc
      _ ≤ Real.exp (-(2 * p)) * Real.exp (2 * p) :=
        mul_le_mul_of_nonneg_left (hcap i) (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hzmean : Real.exp (-(3 * p)) ≤ 𝔼 i, z i := by
    change Real.exp (-(3 * p)) ≤ 𝔼 i, Real.exp (-(2 * p)) * c i
    rw [← Finset.mul_expect]
    have heq : Real.exp (-(3 * p)) = Real.exp (-(2 * p)) * Real.exp (-p) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hcorr (Real.exp_nonneg _)
  obtain ⟨S, hS, hlarge⟩ := exists_dense_level_set z (Real.exp_nonneg (-(3 * p))) hzcap hzmean
  have hhalf : Real.exp (-t) ≤ Real.exp (-(3 * p)) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    calc
      _ ≤ Real.exp (-t) * Real.exp 2 := mul_le_mul_of_nonneg_left
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [t]; ring
  have hzle (i : I) : z i ≤ c i := mul_le_of_le_one_left (hc0 i)
    (Real.exp_le_one_iff.mpr (by linarith))
  have hcharacter (i : I) (hi : i ∈ S) : ∃ χ : AddChar (ZMod N) ℂ,
      Real.exp (-((t + p + A) ^ A)) ≤ ‖finiteFourierCoeff (b i) χ‖ := by
    have hc : Real.exp (-t) ≤ c i := hhalf.trans ((hlarge i hi).trans (hzle i))
    obtain ⟨V⟩ := NativeMeanRowCorrelation.exists_of_expansion
      (Classical.choice (hK i)) ht hc
    exact hfourier V.model (by linarith : 0 ≤ t + p) V.test V.complexity
      (a i) (b i) (ha i) (hb i) V.correlation
  let χ (i : I) : AddChar (ZMod N) ℂ := if hi : i ∈ S then Classical.choose (hcharacter i hi) else 1
  have hmass := dense_set_mean_lower_bound S (fun i => ‖finiteFourierCoeff (b i) (χ i)‖)
    (fun _ => norm_nonneg _) (Real.exp_nonneg (-((t + p + A) ^ A)))
    ((mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg _)).trans hS)
    (fun i hi => by simpa only [χ, dite_eq_left hi] using Classical.choose_spec (hcharacter i hi))
  have hcost : t + (t + p + A) ^ A ≤ (p + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨χ, (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans ?_⟩
  have heq : Real.exp (-(t + (t + p + A) ^ A)) =
      Real.exp (-t) * Real.exp (-((t + p + A) ^ A)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rwa [heq]

end Erdos3

end

end OAI
