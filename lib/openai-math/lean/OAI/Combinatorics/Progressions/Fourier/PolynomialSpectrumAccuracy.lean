import OAI.Combinatorics.Progressions.Fourier.FiniteSpectrumCutoff
import OAI.Combinatorics.Progressions.Polynomial.IndependentPhaseCoefficients

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem product_spectrumTail_levels {B K : Type*} [Fintype B] [Fintype K] [DecidableEq K]
    (c : B → K → ℂ) (S : ℕ → Finset K) (ζ : ℕ → ℝ) (n : ℕ)
    (hζ : ∀ i ≤ n, 0 ≤ ζ i)
    (hsmall : ∀ i ≤ n, ∀ b k, k ∉ S i → ‖c b k‖ ≤ ζ i) :
    spectrumTail (S 0) (fun k => ‖∏ b, c b k‖) ≤
      (∑ i ∈ Finset.range n, (S (i + 1)).card * (ζ i) ^ Fintype.card B) +
        Fintype.card K * (ζ n) ^ Fintype.card B := by
  apply spectrumTail_finite_levels S _ (fun _ => norm_nonneg _) _ n
    (fun i hi => pow_nonneg (hζ i hi) _)
  intro i hi k hk
  exact norm_product_coefficients_le _ (fun b => hsmall i hi b k hk)

theorem product_spectrum_truncation_levels {B K : Type*} [Fintype B] [Fintype K] [DecidableEq K]
    (c : B → K → ℂ) (ψ : K → ℂ) (hψ : ∀ k, ‖ψ k‖ ≤ 1)
    (S : ℕ → Finset K) (ζ : ℕ → ℝ) (n : ℕ)
    (hζ : ∀ i ≤ n, 0 ≤ ζ i)
    (hsmall : ∀ i ≤ n, ∀ b k, k ∉ S i → ‖c b k‖ ≤ ζ i) :
    ‖(∑ k, (∏ b, c b k) * ψ k) - ∑ k ∈ S 0, (∏ b, c b k) * ψ k‖ ≤
      (∑ i ∈ Finset.range n, (S (i + 1)).card * (ζ i) ^ Fintype.card B) +
        Fintype.card K * (ζ n) ^ Fintype.card B :=
  (finite_series_truncation_le (S 0) _ ψ hψ).trans
    (product_spectrumTail_levels c S ζ n hζ hsmall)

theorem product_spectrumTail_geometric {B K : Type*} [Fintype B] [Fintype K] [DecidableEq K]
    (c : B → K → ℂ) (S : ℕ → Finset K) (ζ : ℕ → ℝ) (n : ℕ)
    (hζ : ∀ i ≤ n, 0 ≤ ζ i)
    (hsmall : ∀ i ≤ n, ∀ b k, k ∉ S i → ‖c b k‖ ≤ ζ i)
    {C : ℝ} (hC : 0 ≤ C)
    (hlevel : ∀ i < n, (S (i + 1)).card * (ζ i) ^ Fintype.card B ≤ C * (1 / 2 : ℝ) ^ i) :
    spectrumTail (S 0) (fun k => ‖∏ b, c b k‖) ≤
      2 * C + Fintype.card K * (ζ n) ^ Fintype.card B := by
  apply spectrumTail_finite_geometric S _ (fun _ => norm_nonneg _) _ n
    (fun i hi => pow_nonneg (hζ i hi) _) _ hC hlevel
  intro i hi k hk
  exact norm_product_coefficients_le _ (fun b => hsmall i hi b k hk)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem dyadic_power_ratio {a b : ℕ} (hab : a + 1 ≤ b) (i : ℕ) :
    (2 : ℝ) ^ (a * i) / 2 ^ (b * i) ≤ (1 / 2 : ℝ) ^ i := by
  rw [one_div_pow]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  rw [one_mul, ← pow_add]
  apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
  simpa only [Nat.add_mul, Nat.one_mul] using Nat.mul_le_mul_right i hab

theorem dyadic_level_mass_bound {a b i : ℕ} {C ζ count : ℝ}
    (hab : a + 1 ≤ b) (hC : 0 ≤ C) (hζ : 0 ≤ ζ)
    (hcount : count ≤ C * ((2 : ℝ) ^ a) ^ i) :
    count * (ζ / 2 ^ i) ^ b ≤ (C * ζ ^ b) * (1 / 2 : ℝ) ^ i := by
  calc
    _ ≤ (C * ((2 : ℝ) ^ a) ^ i) * (ζ / 2 ^ i) ^ b :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = (C * ζ ^ b) * ((2 : ℝ) ^ (a * i) / 2 ^ (b * i)) := by
      rw [div_pow, ← pow_mul, ← pow_mul]
      rw [Nat.mul_comm i b]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (dyadic_power_ratio hab i) (by positivity)

theorem product_spectrumTail_dyadic {B K : Type*} [Fintype B] [Fintype K] [DecidableEq K]
    (c : B → K → ℂ) (S : ℕ → Finset K) (n a : ℕ) {C ζ : ℝ}
    (hC : 0 ≤ C) (hζ : 0 ≤ ζ) (hab : a + 1 ≤ Fintype.card B)
    (hcount : ∀ i < n, ((S (i + 1)).card : ℝ) ≤ C * ((2 : ℝ) ^ a) ^ i)
    (hsmall : ∀ i ≤ n, ∀ b k, k ∉ S i → ‖c b k‖ ≤ ζ / 2 ^ i) :
    spectrumTail (S 0) (fun k => ‖∏ b, c b k‖) ≤
      2 * (C * ζ ^ Fintype.card B) + Fintype.card K * (ζ / 2 ^ n) ^ Fintype.card B := by
  apply product_spectrumTail_geometric c S (fun i => ζ / 2 ^ i) n
    (fun _ _ => by positivity) hsmall (by positivity)
  intro i hi
  exact dyadic_level_mass_bound hab hC hζ (hcount i hi)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem cutoff_power_mass_bound {N T δ ζ : ℝ} {p b : ℕ}
    (hT : 0 ≤ T) (hδ : 0 ≤ δ) (hδζ : δ ≤ ζ) (hpb : p ≤ b)
    (hcutoff : N * δ ^ p ≤ T) : N * δ ^ b ≤ T * ζ ^ (b - p) := by
  have he : δ ^ b = δ ^ p * δ ^ (b - p) := by
    rw [← pow_add, Nat.add_sub_of_le hpb]
  rw [he, ← mul_assoc]
  exact (mul_le_mul_of_nonneg_right hcutoff (pow_nonneg hδ _)).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ hδζ _) hT)

theorem dyadic_polynomial_count_factor (A ζ : ℝ) (a i : ℕ) :
    A * ((2 : ℝ) ^ (i + 1) / ζ) ^ a = (A * (2 / ζ) ^ a) * ((2 : ℝ) ^ a) ^ i := by
  simp only [pow_succ', mul_pow, div_pow, ← pow_mul]
  rw [Nat.mul_comm i a]
  ring

theorem polynomial_bias_mass_factor {A ζ : ℝ} {a b : ℕ}
    (hζ : 0 < ζ) (hab : a ≤ b) :
    (A * (2 / ζ) ^ a) * ζ ^ b = A * 2 ^ a * ζ ^ (b - a) := by
  rw [div_pow, pow_sub₀ ζ hζ.ne' hab]
  ring

theorem product_spectrumTail_polynomial_cutoff {B K : Type*}
    [Fintype B] [Fintype K] [DecidableEq K]
    (c : B → K → ℂ) (S : ℕ → Finset K) (n a p : ℕ) {A T ζ : ℝ}
    (hA : 0 ≤ A) (hT : 0 ≤ T) (hζ : 0 < ζ)
    (hab : a + 1 ≤ Fintype.card B) (hpb : p ≤ Fintype.card B)
    (hcount : ∀ i < n, ((S (i + 1)).card : ℝ) ≤ A * (2 ^ (i + 1) / ζ) ^ a)
    (hsmall : ∀ i ≤ n, ∀ b k, k ∉ S i → ‖c b k‖ ≤ ζ / 2 ^ i)
    (hcutoff : (Fintype.card K : ℝ) * (ζ / 2 ^ n) ^ p ≤ T) :
    spectrumTail (S 0) (fun k => ‖∏ b, c b k‖) ≤
      2 * A * 2 ^ a * ζ ^ (Fintype.card B - a) + T * ζ ^ (Fintype.card B - p) := by
  have hc : ∀ i < n, ((S (i + 1)).card : ℝ) ≤
      (A * (2 / ζ) ^ a) * ((2 : ℝ) ^ a) ^ i := by
    intro i hi
    rw [← dyadic_polynomial_count_factor]
    exact hcount i hi
  have ht := product_spectrumTail_dyadic c S n a (by positivity) hζ.le hab hc hsmall
  rw [polynomial_bias_mass_factor hζ (by omega)] at ht
  have hδ : ζ / 2 ^ n ≤ ζ := by
    exact div_le_self hζ.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hb := cutoff_power_mass_bound hT (by positivity) hδ hpb hcutoff
  exact ht.trans (by nlinarith only [hb])

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_spectrum_retained_level {A T ε : ℝ} (hA : 0 ≤ A) (hT : 0 ≤ T)
    (hε : 0 < ε) (a : ℕ) :
    ∃ ζ : ℝ, 0 < ζ ∧ ζ ≤ 1 ∧ (2 * A * 2 ^ a + T) * ζ ≤ ε := by
  let C := 2 * A * 2 ^ a + T
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  let ζ := min 1 (ε / (C + 1))
  have hζ : 0 < ζ := lt_min (by norm_num) (div_pos hε (by linarith))
  refine ⟨ζ, hζ, min_le_left _ _, ?_⟩
  change C * ζ ≤ ε
  calc
    _ ≤ (C + 1) * ζ := mul_le_mul_of_nonneg_right (by linarith) hζ.le
    _ ≤ (C + 1) * (ε / (C + 1)) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (by linarith)
    _ = ε := by field_simp

theorem product_spectrumTail_le_accuracy {B K : Type*}
    [Fintype B] [Fintype K] [DecidableEq K]
    (c : B → K → ℂ) (S : ℕ → Finset K) (n a p : ℕ) {A T ζ ε : ℝ}
    (hA : 0 ≤ A) (hT : 0 ≤ T) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hab : a + 1 ≤ Fintype.card B) (hpb : p + 1 ≤ Fintype.card B)
    (hcount : ∀ i < n, ((S (i + 1)).card : ℝ) ≤ A * (2 ^ (i + 1) / ζ) ^ a)
    (hsmall : ∀ i ≤ n, ∀ b k, k ∉ S i → ‖c b k‖ ≤ ζ / 2 ^ i)
    (hcutoff : (Fintype.card K : ℝ) * (ζ / 2 ^ n) ^ p ≤ T)
    (haccuracy : (2 * A * 2 ^ a + T) * ζ ≤ ε) :
    spectrumTail (S 0) (fun k => ‖∏ b, c b k‖) ≤ ε := by
  have ht := product_spectrumTail_polynomial_cutoff c S n a p hA hT hζ hab (by omega)
    hcount hsmall hcutoff
  have ha : ζ ^ (Fintype.card B - a) ≤ ζ :=
    pow_le_of_le_one hζ.le hζ1 (by omega)
  have hp : ζ ^ (Fintype.card B - p) ≤ ζ :=
    pow_le_of_le_one hζ.le hζ1 (by omega)
  apply ht.trans
  calc
    _ ≤ 2 * A * 2 ^ a * ζ + T * ζ := by gcongr
    _ = (2 * A * 2 ^ a + T) * ζ := by ring
    _ ≤ ε := haccuracy

end Erdos3

end

end OAI
