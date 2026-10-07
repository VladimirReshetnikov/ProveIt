import OAI.Combinatorics.Progressions.Estimates.FlatWeightedComparison

namespace OAI

section

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem correlation_eq_sum_add (L : Finset G) (f g : G → ℝ) (a b : G) :
    correlation L f g (a - b) = (∑ x, f (x + a) * g (x + b)) / L.card := by
  rw [correlation_sub]
  congr 1
  apply Fintype.sum_equiv (Equiv.neg G)
  intro x
  simp [sub_eq_add_neg, add_comm]

theorem correlation_nonneg (L : Finset G) (f g : G → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (t : G) :
    0 ≤ correlation L f g t :=
  div_nonneg (Finset.sum_nonneg (fun x _ => mul_nonneg (hf _) (hg _))) (by positivity)

theorem expect_local_sample_pair (L U : Finset G) (hL : L.Nonempty) (hU : U.Nonempty)
    (f : G → ℝ) (a b : G) {M : ℝ} (hM : 0 < M)
    (hsupport : ∀ x, x ∉ U → f (x + a) * f (x + b) = 0) :
    (𝔼 x : U, (f ((x : G) + a) / M) * (f ((x : G) + b) / M)) =
      ((L.card : ℝ) / ((U.card : ℝ) * M ^ 2)) * correlation L f f (a - b) := by
  have hLc : (L.card : ℝ) ≠ 0 := by exact_mod_cast hL.card_ne_zero
  have hUc : (U.card : ℝ) ≠ 0 := by exact_mod_cast hU.card_ne_zero
  have hsum : (∑ x ∈ U, f (x + a) * f (x + b)) = ∑ x, f (x + a) * f (x + b) := by
    apply Finset.sum_subset (Finset.subset_univ U)
    intro x _ hx
    exact hsupport x hx
  rw [Fintype.expect_eq_sum_div_card,
    Finset.sum_coe_sort U (fun x : G => (f (x + a) / M) * (f (x + b) / M)), Fintype.card_coe]
  simp_rw [div_mul_div_comm, ← pow_two]
  rw [← Finset.sum_div, hsum, correlation_eq_sum_add]
  field_simp

end Erdos3.LocalConvolution

end

end OAI
