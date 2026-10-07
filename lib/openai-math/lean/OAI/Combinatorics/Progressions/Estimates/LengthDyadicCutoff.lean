import Mathlib.Algebra.Order.Archimedean.Basic
import OAI.Combinatorics.Progressions.Fourier.PolynomialSpectrumAccuracy

namespace OAI

section

namespace Erdos3

theorem exists_length_dyadic_cutoff {C L ζ : ℝ} {c : ℕ}
    (hC : 0 < C) (hζ : 0 < ζ) (hc : 0 < c) (hstart : C / ζ ^ c ≤ L) :
    ∃ n : ℕ, (∀ i ≤ n, C / (ζ / 2 ^ i) ^ c ≤ L) ∧
      L * (ζ / 2 ^ n) ^ c ≤ 2 ^ c * C := by
  have hpow : 0 < ζ ^ c := pow_pos hζ _
  have hstart' : C ≤ L * ζ ^ c := (div_le_iff₀ hpow).mp hstart
  have hx : 1 ≤ L * ζ ^ c / C := (le_div_iff₀ hC).mpr (by simpa)
  have hy : (1 : ℝ) < 2 ^ c := one_lt_pow₀ (by norm_num) (by omega)
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near hx hy
  have hswitch (i : ℕ) : ((2 : ℝ) ^ c) ^ i = (2 ^ i) ^ c := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm c i]
  refine ⟨n, ?_, ?_⟩
  · intro i hi
    have hi' : ((2 : ℝ) ^ c) ^ i ≤ L * ζ ^ c / C :=
      (pow_le_pow_right₀ hy.le hi).trans hn
    have hi'' : C * (2 ^ i) ^ c ≤ L * ζ ^ c := by
      have hh := (le_div_iff₀ hC).mp hi'
      rw [hswitch] at hh
      linarith only [hh]
    rw [div_pow]
    apply (div_le_iff₀ (div_pos hpow (by positivity))).mpr
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (2 ^ i) ^ c)).mpr
    exact hi''
  · have hh := (div_lt_iff₀ hC).mp hn'
    rw [pow_succ, hswitch] at hh
    rw [div_pow, ← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 ^ n) ^ c)).mpr
    nlinarith only [hh]

theorem length_cutoff_mass_bound {N V L C δ : ℝ} {c t : ℕ}
    (hV : 0 ≤ V) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hsize : N ≤ V * L ^ t) (hcutoff : L * δ ^ c ≤ C) :
    N * δ ^ (c * t) ≤ V * C ^ t := by
  calc
    _ ≤ (V * L ^ t) * δ ^ (c * t) :=
      mul_le_mul_of_nonneg_right hsize (pow_nonneg hδ _)
    _ = V * (L * δ ^ c) ^ t := by rw [mul_pow, pow_mul]; ring
    _ ≤ V * C ^ t := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (mul_nonneg hL (pow_nonneg hδ _)) hcutoff t) hV

theorem length_small_grid_bound {N V L C ζ : ℝ} {c t : ℕ}
    (hV : 0 ≤ V) (hL : 0 ≤ L)
    (hsize : N ≤ V * L ^ t) (hsmall : L ≤ C / ζ ^ c) :
    N ≤ V * C ^ t / ζ ^ (c * t) := by
  calc
    _ ≤ V * L ^ t := hsize
    _ ≤ V * (C / ζ ^ c) ^ t :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL hsmall t) hV
    _ = _ := by rw [div_pow, pow_mul]; ring

end Erdos3

end

end OAI
