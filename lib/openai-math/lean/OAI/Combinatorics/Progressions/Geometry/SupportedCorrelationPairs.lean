import OAI.Combinatorics.Progressions.Estimates.DenseCorrelationPairs
import OAI.Combinatorics.Progressions.Estimates.RealFiniteZeroExtension

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_supported_correlation_pairs {I X : Type*} [Fintype I] [Nonempty I] [DecidableEq X]
    (A : Finset X) (hA : A.Nonempty) (S : I → Finset X) (hSA : ∀ i, S i ⊆ A)
    (B : X → ℂ) (v : I → X → ℂ) {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ)
    (hB : ∀ x ∈ A, ‖B x‖ ≤ 1) (hv : ∀ i x, x ∈ S i → ‖v i x‖ ≤ 1)
    (hsize : ∀ i, α ≤ (S i).card / (A.card : ℝ))
    (hcorr : ∀ i, δ ≤ ‖𝔼 x ∈ S i, B x * v i x‖) :
    ∃ P : Finset (I × I), P.Nonempty ∧
      (α * δ) ^ 2 / 2 * (Fintype.card I : ℝ) ^ 2 ≤ (P.card : ℝ) ∧
      ∀ t ∈ P, (S t.1 ∩ S t.2).Nonempty ∧
        (α * δ) ^ 2 / 2 ≤ ‖𝔼 x ∈ S t.1 ∩ S t.2, v t.1 x * star (v t.2 x)‖ ∧
        (α * δ) ^ 2 / 2 ≤ (S t.1 ∩ S t.2).card / (A.card : ℝ) := by
  classical
  obtain ⟨x₀, hx₀⟩ := hA
  have hA : A.Nonempty := ⟨x₀, hx₀⟩
  let : Nonempty A := ⟨⟨x₀, hx₀⟩⟩
  let u (i : I) (x : A) := zeroExtendFinset (S i) (v i) x.val
  have huc (i : I) : α * δ ≤ ‖𝔼 x : A, B x.val * u i x‖ := by
    have heq : ‖𝔼 x : A, B x.val * u i x‖ =
        ((S i).card / (A.card : ℝ)) * ‖𝔼 x ∈ S i, B x * v i x‖ := by
      change ‖𝔼 x : A, B x.val * zeroExtendFinset (S i) (v i) x.val‖ = _
      rw [expect_finset_subtype A (fun x => B x * zeroExtendFinset (S i) (v i) x)]
      simp_rw [zeroExtendFinset_mul_left]
      exact norm_expect_zeroExtendFinset A (S i) (hSA i) _
    rw [heq]
    exact mul_le_mul (hsize i) (hcorr i) hδ.le (by positivity)
  obtain ⟨P, hP, hPsize, hPcor⟩ := exists_dense_correlation_pairs
    (fun x : A => B x.val) u (mul_pos hα hδ) (fun x => hB x.val x.property)
    (fun i x => zeroExtendFinset_norm_le_one (S i) (v i) (hv i) x.val) huc
  refine ⟨P, hP, hPsize, ?_⟩
  intro t ht
  have hJA : S t.1 ∩ S t.2 ⊆ A := Finset.Subset.trans Finset.inter_subset_left (hSA t.1)
  have heq : ‖𝔼 x : A, u t.1 x * star (u t.2 x)‖ =
      ((S t.1 ∩ S t.2).card / (A.card : ℝ)) *
        ‖𝔼 x ∈ S t.1 ∩ S t.2, v t.1 x * star (v t.2 x)‖ := by
    change ‖𝔼 x : A, zeroExtendFinset (S t.1) (v t.1) x.val *
      star (zeroExtendFinset (S t.2) (v t.2) x.val)‖ = _
    rw [expect_finset_subtype A (fun x => zeroExtendFinset (S t.1) (v t.1) x *
      star (zeroExtendFinset (S t.2) (v t.2) x))]
    simp_rw [zeroExtendFinset_mul_star]
    exact norm_expect_zeroExtendFinset A (S t.1 ∩ S t.2) hJA _
  have hp := hPcor t ht
  rw [heq] at hp
  have hpos : 0 < (α * δ) ^ 2 / 2 := by positivity
  have hJ : (S t.1 ∩ S t.2).Nonempty := by
    by_contra hempty
    have he : S t.1 ∩ S t.2 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    simp only [he, Finset.card_empty, Nat.cast_zero, zero_div, zero_mul] at hp
    exact (not_le_of_gt hpos) hp
  have hnorm : ‖𝔼 x ∈ S t.1 ∩ S t.2, v t.1 x * star (v t.2 x)‖ ≤ 1 := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply (Finset.expect_le_expect _).trans_eq (Finset.expect_const hJ 1)
    intro x hx
    obtain ⟨hx₁, hx₂⟩ := Finset.mem_inter.mp hx
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hv t.1 x hx₁)).trans (hv t.2 x hx₂)
  have hApos : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hratio : ((S t.1 ∩ S t.2).card / (A.card : ℝ)) ≤ 1 := by
    apply (div_le_iff₀ hApos).mpr
    simpa only [one_mul] using (Nat.cast_le.mpr (Finset.card_le_card hJA) :
      ((S t.1 ∩ S t.2).card : ℝ) ≤ A.card)
  refine ⟨hJ, ?_, ?_⟩
  · exact hp.trans ((mul_le_mul_of_nonneg_right hratio (norm_nonneg _)).trans_eq (one_mul _))
  · exact hp.trans ((mul_le_mul_of_nonneg_left hnorm (by positivity)).trans_eq (mul_one _))

end Erdos3

end

end OAI
