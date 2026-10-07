import OAI.Combinatorics.Progressions.Estimates.BooleanCubeProduct

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_many_family_derivative_correlations {I G : Type*}
    [Fintype I] [Nonempty I] [AddCommGroup G] [Fintype G]
    (f g : I → G → ℂ) (H : Finset I)
    (hf : ∀ i n, ‖f i n‖ ≤ 1) (hg : ∀ i n, ‖g i n‖ ≤ 1)
    {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ)
    (hdense : α * Fintype.card I ≤ (H.card : ℝ))
    (hcorr : ∀ i ∈ H, δ ≤ ‖finiteCorrelation Finset.univ (f i) (g i)‖) :
    ∃ Q : Finset (I × G), Q.Nonempty ∧
      α * δ ^ 2 / 2 * Fintype.card I * Fintype.card G ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, t.1 ∈ H ∧ α * δ ^ 2 / 2 ≤
        ‖finiteCorrelation Finset.univ
          (multiplicativeDerivative (f t.1) t.2) (multiplicativeDerivative (g t.1) t.2)‖ := by
  classical
  let value (t : I × G) := if t.1 ∈ H then
    ‖finiteCorrelation Finset.univ
      (multiplicativeDerivative (f t.1) t.2) (multiplicativeDerivative (g t.1) t.2)‖ else 0
  have hrow (i : I) : (if i ∈ H then δ ^ 2 else 0) ≤ 𝔼 k : G, value (i, k) := by
    by_cases hi : i ∈ H
    · simp only [value, hi, ite_true]
      exact (pow_le_pow_left₀ hδ.le (hcorr i hi) 2).trans
        (correlation_sq_le_expect_norm_derivative (f i) (g i))
    · simp only [value, hi, ite_false, Fintype.expect_const, le_refl]
  have hcard : (0 : ℝ) < Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  have hindicator : (𝔼 i : I, if i ∈ H then δ ^ 2 else 0) =
      (H.card : ℝ) * δ ^ 2 / Fintype.card I := by
    rw [Fintype.expect_eq_sum_div_card]
    simp
  have hmean : α * δ ^ 2 ≤ 𝔼 t : I × G, value t := by
    calc
      _ ≤ (H.card : ℝ) * δ ^ 2 / Fintype.card I := by
        apply (le_div_iff₀ hcard).mpr
        nlinarith [mul_le_mul_of_nonneg_right hdense (sq_nonneg δ)]
      _ = (𝔼 i : I, if i ∈ H then δ ^ 2 else 0) := hindicator.symm
      _ ≤ 𝔼 i : I, 𝔼 k : G, value (i, k) := Finset.expect_le_expect (fun i _ => hrow i)
      _ = _ := by rw [← Finset.expect_product, Finset.univ_product_univ]
  have hcap (t : I × G) : value t ≤ 1 := by
    by_cases ht : t.1 ∈ H
    · simp only [value, ht, ite_true]
      simpa only [one_pow] using norm_derivativeCorrelation_le (f t.1) (g t.1) (hf t.1) (hg t.1) t.2
    · simp only [value, ht, ite_false, zero_le_one]
  obtain ⟨Q, hQsize, hQcorr⟩ :=
    exists_dense_level_set value (by positivity : 0 ≤ α * δ ^ 2) hcap hmean
  have hsize : α * δ ^ 2 / 2 * Fintype.card I * Fintype.card G ≤ (Q.card : ℝ) := by
    simpa only [Fintype.card_prod, Nat.cast_mul, mul_assoc] using hQsize
  have hI : (0 : ℝ) < Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  have hG : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  have hQ : Q.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast lt_of_lt_of_le
      (by positivity : 0 < α * δ ^ 2 / 2 * (Fintype.card I : ℝ) * Fintype.card G) hsize
  refine ⟨Q, hQ, hsize, ?_⟩
  intro t ht
  have hm : t.1 ∈ H := by
    by_contra hn
    have hpos : 0 < value t := lt_of_lt_of_le (by positivity) (hQcorr t ht)
    simp only [value, hn, ite_false, lt_self_iff_false] at hpos
  exact ⟨hm, by simpa only [value, hm, ite_true] using hQcorr t ht⟩

end Erdos3

end

end OAI
