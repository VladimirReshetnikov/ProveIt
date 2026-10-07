import OAI.Combinatorics.Progressions.Estimates.MultiaffineExpansion
import OAI.Combinatorics.Progressions.Fourier.BoxDifferenceCharacter

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

theorem norm_affine_fin_phase_mean (M : ℕ) (a b : ℝ) :
    ‖𝔼 t : Fin M, character ((a*(t.val : ℝ)+b : ℝ) : CircleFourier.Circle)‖ =
      ‖geometricCharacterMean M (a : CircleFourier.Circle)‖ := by
  have he (t : Fin M) :
      character ((a*(t.val : ℝ)+b : ℝ) : CircleFourier.Circle) =
        character (b : CircleFourier.Circle) * character (t.val • (a : CircleFourier.Circle)) := by
    have hr : a*(t.val : ℝ)+b = b+t.val • a := by simp only [nsmul_eq_mul]; ring
    rw [hr, AddCircle.coe_add, AddCircle.coe_nsmul, character_add]
  simp_rw [he]
  rw [← Finset.mul_expect, norm_mul, norm_character, one_mul]
  rfl

noncomputable def multiaffineIntervalPhase {n : ℕ} {N : Fin n → ℕ} {M : ℕ}
    (a b : Finset (Fin n) → ℝ) (u : Fin n → ℝ) (w : ℝ)
    (x : ∀ i, Fin (N i)) (t : Fin M) : ℂ :=
  character ((multiaffineExpansion (fun S => a S*(w+(t.val : ℝ))+b S)
    (fun i => u i+((x i).val : ℝ)) : ℝ) : CircleFourier.Circle)

theorem multiaffine_phase_difference_mean {n : ℕ} (N : Fin n → ℕ) (M : ℕ)
    (a b : Finset (Fin n) → ℝ) (u : Fin n → ℝ) (w : ℝ)
    (x y : ∀ i, Fin (N i)) :
    ‖𝔼 t : Fin M, iteratedBoxDifference n (multiaffineIntervalPhase a b u w) x y t‖ =
      ‖geometricCharacterMean M
        ((a Finset.univ * ∏ i, (((x i).val : ℝ)-((y i).val : ℝ)) : ℝ) : CircleFourier.Circle)‖ := by
  unfold multiaffineIntervalPhase
  simp_rw [iteratedBoxDifference_character,
    multiaffineExpansion_box_difference n
      (fun S (t : Fin M) => a S*(w+(t.val : ℝ))+b S)
      (fun i (j : Fin (N i)) => u i+(j.val : ℝ)), add_sub_add_left_eq_sub]
  let D := ∏ i, (((x i).val : ℝ)-((y i).val : ℝ))
  change ‖𝔼 t : Fin M,
    character (((a Finset.univ*(w+(t.val : ℝ))+b Finset.univ)*D : ℝ) : CircleFourier.Circle)‖ =
      ‖geometricCharacterMean M (a Finset.univ*D : CircleFourier.Circle)‖
  have he (t : Fin M) : (a Finset.univ*(w+(t.val : ℝ))+b Finset.univ)*D =
      (a Finset.univ*D)*(t.val : ℝ)+(a Finset.univ*w+b Finset.univ)*D := by ring
  simp_rw [he]
  exact norm_affine_fin_phase_mean M _ _

theorem multiaffine_phase_box_bias {n : ℕ} (N : Fin n → ℕ) (hN : ∀ i, 0 < N i)
    (M : ℕ) (hM : 0 < M) (a b : Finset (Fin n) → ℝ) (u : Fin n → ℝ) (w : ℝ)
    {ζ : ℝ} (hζ : 0 ≤ ζ)
    (hbias : ζ ≤ ‖𝔼 x : ∀ i, Fin (N i), 𝔼 t : Fin M, multiaffineIntervalPhase a b u w x t‖) :
    ζ^(2^n) ≤ 𝔼 y : (∀ i, Fin (N i)), 𝔼 x : (∀ i, Fin (N i)),
      ‖geometricCharacterMean M
        ((a Finset.univ * ∏ i, (((x i).val : ℝ)-((y i).val : ℝ)) : ℝ) : CircleFourier.Circle)‖ := by
  let : ∀ i, Nonempty (Fin (N i)) := fun i => ⟨⟨0, hN i⟩⟩
  let : Nonempty (Fin M) := ⟨⟨0,hM⟩⟩
  have h := (pow_le_pow_left₀ hζ hbias (2^n)).trans
    (iterated_box_cauchy_schwarz n (multiaffineIntervalPhase a b u w))
  simp_rw [multiaffine_phase_difference_mean] at h
  rwa [Finset.expect_comm] at h

end Erdos3

end

end OAI
