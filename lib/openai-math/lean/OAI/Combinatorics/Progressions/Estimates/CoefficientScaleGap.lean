import OAI.Combinatorics.Progressions.Probability.ShiftedSmoothLawBounds

namespace OAI

section

namespace Erdos3

theorem exists_unoccupied_coefficient_gap {I : Type*} [Fintype I]
    (x : I → ℝ) (b : I → ℕ → ℝ) (hb : ∀ i, Monotone (b i)) :
    ∃ j : Fin (Fintype.card I + 1), ∀ i, ¬(b i j.val < x i ∧ x i < b i (j.val + 1)) := by
  classical
  by_contra h
  push Not at h
  choose f hf using h
  have hinj : Function.Injective f := by
    intro a c hac
    apply Fin.ext
    rcases lt_trichotomy a.val c.val with hlt | heq | hgt
    · have hstep := hb (f a) (show a.val + 1 ≤ c.val by omega)
      have hc := (hf c).1
      rw [← hac] at hc
      linarith [(hf a).2]
    · exact heq
    · have hstep := hb (f c) (show c.val + 1 ≤ a.val by omega)
      have ha := (hf a).1
      rw [hac] at ha
      linarith [(hf c).2]
  have hcard := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin] at hcard
  omega

theorem exists_integer_coefficient_scale_gap {I : Type*} [Fintype I]
    (K : I → ℝ) (h : I → ℕ) (L₀ A : ℕ) (hL₀ : 0 < L₀) (hA : 1 ≤ A) :
    ∃ L : ℕ, 0 < L ∧ L₀ ≤ L ∧ L ≤ L₀ * A ^ Fintype.card I ∧
      ∀ i, (L : ℝ) ^ h i < K i → ((A : ℝ) * L) ^ h i ≤ K i := by
  let b : I → ℕ → ℝ := fun i j => ((L₀ * A ^ j : ℕ) : ℝ) ^ h i
  have hb : ∀ i, Monotone (b i) := by
    intro i j k hjk
    apply pow_le_pow_left₀ (Nat.cast_nonneg _)
    exact_mod_cast Nat.mul_le_mul_left L₀ (Nat.pow_le_pow_right (by omega : 0 < A) hjk)
  obtain ⟨j, hj⟩ := exists_unoccupied_coefficient_gap K b hb
  refine ⟨L₀ * A ^ j.val, Nat.mul_pos hL₀ (pow_pos (by omega) _), ?_, ?_, ?_⟩
  · have hp : 1 ≤ A ^ j.val := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
    nlinarith
  · exact Nat.mul_le_mul_left L₀ (Nat.pow_le_pow_right (by omega) (by omega : j.val ≤ Fintype.card I))
  · intro i hi
    have hbound : b i (j.val + 1) ≤ K i := le_of_not_gt (fun hlt => hj i ⟨hi, hlt⟩)
    have he : ((L₀ * A ^ (j.val + 1) : ℕ) : ℝ) = (A : ℝ) * (L₀ * A ^ j.val : ℕ) := by
      push_cast
      rw [pow_succ]
      ring
    simpa only [b, he] using hbound

theorem coefficient_gap_principal_width {K L A γ : ℝ} {h : ℕ}
    (hL : 0 < L) (hA : 1 ≤ A) (hγ : 0 < γ) (hh : 1 ≤ h)
    (hgap : (A * L) ^ h ≤ K)
    (hwidth : 16 * (probabilityProfileLipschitz : ℝ) ≤ γ * A) :
    8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / L ^ h) := by
  have hpow : A ≤ A ^ h := by simpa only [pow_one] using pow_le_pow_right₀ hA hh
  have hratio : A ≤ K / L ^ h := (le_div_iff₀ (pow_pos hL h)).mpr (by
    calc
      A * L ^ h ≤ A ^ h * L ^ h := mul_le_mul_of_nonneg_right hpow (pow_pos hL h).le
      _ = (A * L) ^ h := (mul_pow A L h).symm
      _ ≤ K := hgap)
  have hm := mul_le_mul_of_nonneg_left hratio hγ.le
  nlinarith

end Erdos3

end

end OAI
