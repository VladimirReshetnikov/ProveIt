import OAI.Combinatorics.Progressions.Fourier.FrequencyGridIntervals

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def rationalGridMajorSet (M Q H : ℕ) : Finset (Fin M) :=
  (Finset.range (Q + 1)).biUnion fun d =>
    (Finset.Icc (-(Q * (H + 1) : ℤ)) (Q * (H + 1) : ℤ)).biUnion fun a =>
      frequencyGridInterval M ((M : ℝ) * ((a : ℝ) / d)) H

theorem mem_rationalGridMajorSet {M Q H d : ℕ} (hM : 0 < M) (hd : 0 < d) (hdQ : d ≤ Q)
    (k : Fin M) (a : ℤ) (hclose : |(k.val : ℝ) - M * ((a : ℝ) / d)| ≤ H) :
    k ∈ rationalGridMajorSet M Q H := by
  classical
  have ha := grid_approximation_numerator_bound hM hd hdQ k a hclose
  unfold rationalGridMajorSet
  apply Finset.mem_biUnion.mpr
  refine ⟨d, Finset.mem_range.mpr (by omega), Finset.mem_biUnion.mpr ?_⟩
  refine ⟨a, Finset.mem_Icc.mpr (abs_le.mp ha), ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hclose⟩

theorem integerSymmetricInterval_card (B : ℕ) :
    (Finset.Icc (-(B : ℤ)) (B : ℤ)).card = 2 * B + 1 := by
  rw [Int.card_Icc]
  omega

theorem rationalGridMajorSet_card (M Q H : ℕ) :
    ((rationalGridMajorSet M Q H).card : ℝ) ≤
      (Q + 1 : ℝ) * (2 * Q * (H + 1) + 1) * (2 * H + 1) := by
  classical
  let A := Finset.Icc (-(Q * (H + 1) : ℤ)) (Q * (H + 1) : ℤ)
  have hA : (A.card : ℝ) = 2 * Q * (H + 1) + 1 := by
    have h := integerSymmetricInterval_card (Q * (H + 1))
    dsimp only [A]
    norm_cast at h ⊢
    simpa only [Nat.mul_assoc] using h
  have hd (d : ℕ) :
      ((A.biUnion fun a => frequencyGridInterval M ((M : ℝ) * ((a : ℝ) / d)) H).card : ℝ) ≤
        (2 * Q * (H + 1) + 1) * (2 * H + 1) := by
    calc
      _ ≤ ∑ a ∈ A, ((frequencyGridInterval M ((M : ℝ) * ((a : ℝ) / d)) H).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ A, (2 * (H : ℝ) + 1) :=
        Finset.sum_le_sum (fun a _ => frequencyGridInterval_card M _ (Nat.cast_nonneg H))
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hA]
  unfold rationalGridMajorSet
  calc
    _ ≤ ∑ d ∈ Finset.range (Q + 1),
        ((A.biUnion fun a => frequencyGridInterval M ((M : ℝ) * ((a : ℝ) / d)) H).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _d ∈ Finset.range (Q + 1), ((2 * (Q : ℝ) * (H + 1) + 1) * (2 * H + 1)) :=
      Finset.sum_le_sum (fun d _ => hd d)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]; ring

noncomputable def rationalGridMajorBox (J : Type*) [Fintype J] [DecidableEq J]
    (M Q H : ℕ) : Finset (J → Fin M) :=
  Fintype.piFinset (fun _ => rationalGridMajorSet M Q H)

theorem rationalGridMajorBox_card (J : Type*) [Fintype J] [DecidableEq J] (M Q H : ℕ) :
    ((rationalGridMajorBox J M Q H).card : ℝ) ≤
      ((Q + 1 : ℝ) * (2 * Q * (H + 1) + 1) * (2 * H + 1)) ^ Fintype.card J := by
  classical
  unfold rationalGridMajorBox
  rw [Fintype.card_piFinset]
  simp only [Finset.prod_const, Finset.card_univ, Nat.cast_pow]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (rationalGridMajorSet_card M Q H) _

end Erdos3

end

end OAI
