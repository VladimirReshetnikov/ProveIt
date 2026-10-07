/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Dynamics.MultiaffineBiasBudget
import OAI.Combinatorics.Progressions.Estimates.LengthDyadicCutoff
import OAI.Combinatorics.Progressions.Geometry.GeometricLocalizationThreshold
import OAI.Combinatorics.Progressions.Polynomial.PolynomialGridCover

namespace OAI

section

namespace Erdos3

theorem unscale_grid_interval {M H d : ℕ} (hM : 0 < M) (k : Fin M) (a : ℤ)
    (h : |(k.val : ℝ) - M * ((a : ℝ) / d)| ≤ H) :
    |(k.val : ℝ) / M - (a : ℝ) / d| ≤ (H : ℝ) / M := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have he : (k.val : ℝ) / M - (a : ℝ) / d =
      ((k.val : ℝ) - M * ((a : ℝ) / d)) / M := by field_simp
  rw [he, abs_div, abs_of_pos hM']
  exact div_le_div_of_nonneg_right h hM'.le

theorem rationalGridMajorSet_rational {M Q H : ℕ} (hM : 0 < M) (k : Fin M)
    (hk : k ∈ rationalGridMajorSet M Q H) :
    ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ (Q + 1 : ℝ) ∧
      ∃ a : ℤ, |(k.val : ℝ) / M - (a : ℝ) / d| ≤ (H : ℝ) / M := by
  classical
  obtain ⟨d, hd, ha⟩ := Finset.mem_biUnion.mp hk
  obtain ⟨a, _, hk⟩ := Finset.mem_biUnion.mp ha
  have he := (Finset.mem_filter.mp hk).2
  by_cases hd0 : d = 0
  · refine ⟨1, by omega, by exact_mod_cast (show 1 ≤ Q + 1 by omega), 0, ?_⟩
    apply unscale_grid_interval hM k 0
    simpa only [hd0, Nat.cast_zero, div_zero, Int.cast_zero, zero_div, mul_zero, sub_zero] using he
  · refine ⟨d, Nat.pos_of_ne_zero hd0, ?_, a, unscale_grid_interval hM k a he⟩
    exact_mod_cast (Finset.mem_range.mp hd).le

theorem rationalGridMajorBox_character {J : Type*} [Fintype J] [DecidableEq J]
    {M Q H : ℕ} (hM : 0 < M) (k : J → Fin M) (hk : k ∈ rationalGridMajorBox J M Q H) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ (Q + 1 : ℝ) ^ Fintype.card J ∧
      ∃ (a : J → ℤ) (ξ : J → ℝ), (∀ j, |ξ j| ≤ H) ∧
        ∀ j, ((k j).val : ℝ) / M = (a j : ℝ) / D + ξ j / M := by
  have hj := Fintype.mem_piFinset.mp hk
  obtain ⟨D, hD, hDQ, a, ha⟩ := exists_common_rational_approximations
    (fun j => ((k j).val : ℝ) / M) (fun j => rationalGridMajorSet_rational hM (k j) (hj j))
  let ξ j := (M : ℝ) * (((k j).val : ℝ) / M - (a j : ℝ) / D)
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  refine ⟨D, hD, hDQ, a, ξ, ?_, ?_⟩
  · intro j
    dsimp only [ξ]
    rw [abs_mul, abs_of_pos hM']
    calc
      _ ≤ (M : ℝ) * ((H : ℝ) / M) := mul_le_mul_of_nonneg_left (ha j) hM'.le
      _ = H := by field_simp
  · intro j
    dsimp only [ξ]
    field_simp
    ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def lengthAwareSpectrumCover {K : Type*} [Fintype K]
    (C L : ℝ) (c : ℕ) (cover : ℝ → Finset K) (ζ : ℝ) : Finset K := by
  classical
  exact if C / ζ ^ c ≤ L then cover ζ else Finset.univ

theorem lengthAwareSpectrumCover_card {K : Type*} [Fintype K]
    (cover : ℝ → Finset K) {C L V A ζ : ℝ} {c t a : ℕ}
    (hL : 0 ≤ L) (hV : 0 ≤ V) (hA : 0 ≤ A) (hC : 0 ≤ C) (hζ : 0 < ζ)
    (hsize : (Fintype.card K : ℝ) ≤ V * L ^ t)
    (hcover : ((cover ζ).card : ℝ) ≤ A / ζ ^ a) :
    ((lengthAwareSpectrumCover C L c cover ζ).card : ℝ) ≤
      A / ζ ^ a + V * C ^ t / ζ ^ (c * t) := by
  classical
  unfold lengthAwareSpectrumCover
  split_ifs with hstart
  · exact hcover.trans (le_add_of_nonneg_right (by positivity))
  · rw [Finset.card_univ]
    have hb := length_small_grid_bound hV hL hsize (le_of_lt (lt_of_not_ge hstart))
    exact hb.trans (le_add_of_nonneg_left (by positivity))

theorem lengthAwareSpectrumCover_accuracy {B K : Type*}
    [Fintype B] [Fintype K] [DecidableEq K]
    (coeff : B → K → ℂ) (cover : ℝ → Finset K) {C L V A ζ ε : ℝ} {c t a : ℕ}
    (hC : 0 < C) (hL : 0 ≤ L) (hV : 0 ≤ V) (hA : 0 ≤ A)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hε : 0 ≤ ε) (hc : 0 < c)
    (haB : a + 1 ≤ Fintype.card B) (htB : c * t + 1 ≤ Fintype.card B)
    (hsize : (Fintype.card K : ℝ) ≤ V * L ^ t)
    (hcover : ∀ δ, 0 < δ → δ ≤ 1 → ((cover δ).card : ℝ) ≤ A / δ ^ a)
    (hminor : ∀ δ, 0 < δ → δ ≤ 1 → C / δ ^ c ≤ L →
      ∀ b k, k ∉ cover δ → ‖coeff b k‖ ≤ δ)
    (haccuracy : (2 * A * 2 ^ a + V * (2 ^ c * C) ^ t) * ζ ≤ ε) :
    spectrumTail (lengthAwareSpectrumCover C L c cover ζ)
      (fun k => ‖∏ b, coeff b k‖) ≤ ε := by
  classical
  by_cases hstart : C / ζ ^ c ≤ L
  · obtain ⟨n, hn, hlast⟩ := exists_length_dyadic_cutoff hC hζ hc hstart
    have hδ (i : ℕ) : 0 < ζ / 2 ^ i ∧ ζ / 2 ^ i ≤ 1 := by
      refine ⟨by positivity, ?_⟩
      exact (div_le_self hζ.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))).trans hζ1
    have hb := length_cutoff_mass_bound hV hL (hδ n).1.le hsize hlast
    have hcount (i : ℕ) (_hi : i < n) :
        ((cover (ζ / 2 ^ (i + 1))).card : ℝ) ≤ A * (2 ^ (i + 1) / ζ) ^ a := by
      have hh := hcover (ζ / 2 ^ (i + 1)) (hδ _).1 (hδ _).2
      apply hh.trans_eq
      simp only [div_pow, div_div_eq_mul_div]
      ring
    have hsmall (i : ℕ) (hi : i ≤ n) :=
      hminor (ζ / 2 ^ i) (hδ i).1 (hδ i).2 (hn i hi)
    have ht := product_spectrumTail_le_accuracy coeff (fun i => cover (ζ / 2 ^ i))
      n a (c * t) hA (by positivity) hζ hζ1 haB htB hcount hsmall hb haccuracy
    simpa only [lengthAwareSpectrumCover, ite_eq_left hstart, pow_zero, div_one] using ht
  · simpa only [lengthAwareSpectrumCover, ite_eq_right hstart, spectrumTail,
      Finset.mem_univ, ite_true, Finset.sum_const_zero] using hε

theorem exists_lengthAwareSpectrum_accuracy {B K : Type*}
    [Fintype B] [Fintype K] [DecidableEq K]
    (coeff : B → K → ℂ) (cover : ℝ → Finset K) {C L V A ε : ℝ} {c t a : ℕ}
    (hC : 0 < C) (hL : 0 ≤ L) (hV : 0 ≤ V) (hA : 0 ≤ A) (hε : 0 < ε) (hc : 0 < c)
    (haB : a + 1 ≤ Fintype.card B) (htB : c * t + 1 ≤ Fintype.card B)
    (hsize : (Fintype.card K : ℝ) ≤ V * L ^ t)
    (hcover : ∀ δ, 0 < δ → δ ≤ 1 → ((cover δ).card : ℝ) ≤ A / δ ^ a)
    (hminor : ∀ δ, 0 < δ → δ ≤ 1 → C / δ ^ c ≤ L →
      ∀ b k, k ∉ cover δ → ‖coeff b k‖ ≤ δ) :
    ∃ ζ : ℝ, 0 < ζ ∧ ζ ≤ 1 ∧
      ((lengthAwareSpectrumCover C L c cover ζ).card : ℝ) ≤
        A / ζ ^ a + V * C ^ t / ζ ^ (c * t) ∧
      spectrumTail (lengthAwareSpectrumCover C L c cover ζ)
        (fun k => ‖∏ b, coeff b k‖) ≤ ε := by
  obtain ⟨ζ, hζ, hζ1, hacc⟩ := exists_spectrum_retained_level hA
    (show 0 ≤ V * (2 ^ c * C) ^ t by positivity) hε a
  refine ⟨ζ, hζ, hζ1, ?_, ?_⟩
  · exact lengthAwareSpectrumCover_card cover hL hV hA hC.le hζ hsize (hcover ζ hζ hζ1)
  · exact lengthAwareSpectrumCover_accuracy coeff cover hC hL hV hA hζ hζ1 hε.le hc
      haB htB hsize hcover hminor hacc

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem rationalGridMajorBox_scaled_character {J : Type*} [Fintype J] [DecidableEq J]
    {K M Q H : ℕ} (hK : 0 < K) (hKM : K ≤ M)
    (k : J → Fin M) (hk : k ∈ rationalGridMajorBox J M Q H) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ (Q + 1 : ℝ) ^ Fintype.card J ∧
      ∃ (a : J → ℤ) (ω : J → ℝ), (∀ j, |ω j| ≤ H) ∧
        ∀ j, ((k j).val : ℝ) / M = (a j : ℝ) / D + ω j / K := by
  have hM : 0 < M := lt_of_lt_of_le hK hKM
  have hK0 : (K : ℝ) ≠ 0 := (Nat.cast_pos.mpr hK).ne'
  have hM0 : (M : ℝ) ≠ 0 := (Nat.cast_pos.mpr hM).ne'
  obtain ⟨D, hD, hDQ, a, ξ, hξ, he⟩ := rationalGridMajorBox_character hM k hk
  refine ⟨D, hD, hDQ, a, (fun j => (K : ℝ) * ξ j / M), ?_, ?_⟩
  · intro j
    simp only [abs_div, abs_mul, abs_of_nonneg (Nat.cast_nonneg K : (0 : ℝ) ≤ K),
      abs_of_nonneg (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
    apply (div_le_iff₀ (Nat.cast_pos.mpr hM)).mpr
    calc
      (K : ℝ) * |ξ j| ≤ (K : ℝ) * H := mul_le_mul_of_nonneg_left (hξ j) (Nat.cast_nonneg K)
      _ ≤ (M : ℝ) * H := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hKM) (Nat.cast_nonneg H)
      _ = (H : ℝ) * M := mul_comm _ _
  · intro j
    rw [he j]
    congr 1
    field_simp

theorem lengthAwarePolynomialGrid_character {J : Type*} [Fintype J] [DecidableEq J]
    {K M : ℕ} (hK : 0 < K) (hKM : K ≤ M)
    {C L V A ζ : ℝ} {c t r : ℕ} (hL : 0 ≤ L) (hV : 0 ≤ V)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ V * L ^ t)
    (k : J → Fin M)
    (hk : k ∈ lengthAwareSpectrumCover C L c (polynomialGridCover J M A r) ζ) :
    ∃ D : ℕ, 0 < D ∧
      (D : ℝ) ≤ max ((⌈A / ζ ^ r⌉₊ + 1 : ℝ) ^ Fintype.card J)
        (V * C ^ t / ζ ^ (c * t)) ∧
      ∃ (a : J → ℤ) (ω : J → ℝ), (∀ j, |ω j| ≤ (⌈A / ζ ^ r⌉₊ : ℝ)) ∧
        ∀ j, ((k j).val : ℝ) / M = (a j : ℝ) / D + ω j / K := by
  classical
  by_cases hstart : C / ζ ^ c ≤ L
  · have hk' : k ∈ rationalGridMajorBox J M ⌈A / ζ ^ r⌉₊ ⌈A / ζ ^ r⌉₊ := by
      simpa only [lengthAwareSpectrumCover, ite_eq_left hstart, polynomialGridCover] using hk
    obtain ⟨D, hD, hb, a, ω, hω, he⟩ := rationalGridMajorBox_scaled_character hK hKM k hk'
    exact ⟨D, hD, hb.trans (le_max_left _ _), a, ω, hω, he⟩
  · cases isEmpty_or_nonempty J with
    | inl hJ =>
      let := hJ
      refine ⟨1, Nat.zero_lt_one, ?_, (fun j => isEmptyElim j),
        (fun j => isEmptyElim j), (fun j => isEmptyElim j), (fun j => isEmptyElim j)⟩
      simpa only [Fintype.card_eq_zero, pow_zero, Nat.cast_one] using
        (le_max_left (1 : ℝ) (V * C ^ t / ζ ^ (c * t)))
    | inr hJ =>
      let := hJ
      have hM : 0 < M := lt_of_lt_of_le hK hKM
      have hpow : (M : ℝ) ≤ (M : ℝ) ^ Fintype.card J :=
        le_self_pow₀ (by exact_mod_cast hM) (Fintype.card_pos.ne')
      have hb := length_small_grid_bound hV hL hsize (le_of_lt (lt_of_not_ge hstart))
      refine ⟨M, hM, (hpow.trans hb).trans (le_max_right _ _),
        (fun j => ((k j).val : ℤ)), (fun _ => 0), ?_, ?_⟩
      · intro j
        simpa only [abs_zero] using (Nat.cast_nonneg ⌈A / ζ ^ r⌉₊ : (0 : ℝ) ≤ _)
      · intro j
        simp only [Int.cast_natCast, zero_div, add_zero]

end Erdos3

end

section

namespace Erdos3

noncomputable def localizedMajorArcBudget (n : ℕ) (U ζ : ℝ) : ℝ :=
  multiaffineBiasBudget n (localizationThreshold U ζ (n + 1))

noncomputable def localizedMajorArcLengthBudget (n : ℕ) (U ζ : ℝ) : ℝ :=
  localizationLengthBudget U (localizationThreshold U ζ (n + 1))
    (localizedMajorArcBudget n U ζ + 1)

noncomputable def localizedMajorArcErrorBudget (n : ℕ) (U ζ : ℝ) : ℝ :=
  localizedMajorArcBudget n U ζ *
    (localizationLengthBudget U (localizationThreshold U ζ (n + 1)) 1) ^ (n + 1)

theorem localizedMajorArcBudget_pos (n : ℕ) {U ζ : ℝ} (hU : 1 ≤ U) (hζ : 0 < ζ) :
    0 < localizedMajorArcBudget n U ζ :=
  multiaffineBiasBudget_pos n (localizationThreshold_pos hU hζ (n + 1))

end Erdos3

end

section

namespace Erdos3

theorem localizationLengthBudget_threshold_eq (U ζ W : ℝ) (m : ℕ) :
    localizationLengthBudget U (localizationThreshold U ζ m) W =
      256 * U ^ 6 * W * (2 * U ^ 2) ^ (m * 2) / ζ ^ 2 := by
  simp only [localizationLengthBudget, localizationThreshold, div_pow, div_div_eq_mul_div, pow_mul]

theorem localizedMajorArcBudget_eq_power (n : ℕ) {U ζ : ℝ}
    (hU : 1 ≤ U) (hζ : 0 < ζ) :
    localizedMajorArcBudget n U ζ =
      ((denseProductDensityConstant n : ℝ) * (2 * 3 ^ n) ^ denseProductExponent n) *
        (2 * U ^ 2) ^ ((n + 1) * (2 ^ n * (denseProductExponent n + 1))) /
          ζ ^ (2 ^ n * (denseProductExponent n + 1)) := by
  unfold localizedMajorArcBudget
  rw [multiaffineBiasBudget_eq_power n (localizationThreshold_pos hU hζ (n + 1))]
  simp only [localizationThreshold, div_pow, div_div_eq_mul_div, pow_mul]

theorem localizedMajorArcLengthBudget_eq (n : ℕ) (U ζ : ℝ) :
    localizedMajorArcLengthBudget n U ζ =
      256 * U ^ 6 * (localizedMajorArcBudget n U ζ + 1) *
        (2 * U ^ 2) ^ ((n + 1) * 2) / ζ ^ 2 :=
  localizationLengthBudget_threshold_eq U ζ (localizedMajorArcBudget n U ζ + 1) (n + 1)

theorem localizedMajorArcErrorBudget_eq (n : ℕ) (U ζ : ℝ) :
    localizedMajorArcErrorBudget n U ζ =
      localizedMajorArcBudget n U ζ *
        (256 * U ^ 6 * (2 * U ^ 2) ^ ((n + 1) * 2) / ζ ^ 2) ^ (n + 1) := by
  unfold localizedMajorArcErrorBudget
  rw [localizationLengthBudget_threshold_eq]
  simp only [mul_one]

end Erdos3

end

section

namespace Erdos3

def majorArcBiasExponent (n : ℕ) : ℕ := 2 ^ n * (denseProductExponent n + 1)

noncomputable def majorArcBiasConstant (n : ℕ) (U : ℝ) : ℝ :=
  ((denseProductDensityConstant n : ℝ) * (2 * 3 ^ n) ^ denseProductExponent n) *
    (2 * U ^ 2) ^ ((n + 1) * majorArcBiasExponent n)

noncomputable def majorArcLocalizationConstant (n : ℕ) (U : ℝ) : ℝ :=
  256 * U ^ 6 * (2 * U ^ 2) ^ ((n + 1) * 2)

def majorArcLengthExponent (n : ℕ) : ℕ := majorArcBiasExponent n + 2

noncomputable def majorArcLengthConstant (n : ℕ) (U : ℝ) : ℝ :=
  majorArcLocalizationConstant n U * (majorArcBiasConstant n U + 1)

def majorArcErrorExponent (n : ℕ) : ℕ := majorArcBiasExponent n + 2 * (n + 1)

noncomputable def majorArcErrorConstant (n : ℕ) (U : ℝ) : ℝ :=
  majorArcBiasConstant n U * majorArcLocalizationConstant n U ^ (n + 1)

theorem majorArcBiasConstant_pos (n : ℕ) {U : ℝ} (hU : 1 ≤ U) :
    0 < majorArcBiasConstant n U := by
  have h := localizedMajorArcBudget_pos n hU (by norm_num : (0 : ℝ) < 1)
  rw [localizedMajorArcBudget_eq_power n hU (by norm_num)] at h
  simpa only [majorArcBiasConstant, majorArcBiasExponent, one_pow, div_one] using h

theorem majorArcLocalizationConstant_pos (n : ℕ) {U : ℝ} (hU : 1 ≤ U) :
    0 < majorArcLocalizationConstant n U := by
  have : 0 < U := lt_of_lt_of_le (by norm_num) hU
  unfold majorArcLocalizationConstant
  positivity

theorem majorArcLengthConstant_pos (n : ℕ) {U : ℝ} (hU : 1 ≤ U) :
    0 < majorArcLengthConstant n U := by
  have := majorArcBiasConstant_pos n hU
  have := majorArcLocalizationConstant_pos n hU
  unfold majorArcLengthConstant
  positivity

theorem majorArcErrorConstant_pos (n : ℕ) {U : ℝ} (hU : 1 ≤ U) :
    0 < majorArcErrorConstant n U := by
  have := majorArcBiasConstant_pos n hU
  have := majorArcLocalizationConstant_pos n hU
  unfold majorArcErrorConstant
  positivity

theorem localizedMajorArcBudget_constant (n : ℕ) {U ζ : ℝ}
    (hU : 1 ≤ U) (hζ : 0 < ζ) :
    localizedMajorArcBudget n U ζ = majorArcBiasConstant n U / ζ ^ majorArcBiasExponent n :=
  localizedMajorArcBudget_eq_power n hU hζ

theorem localizedMajorArcLengthBudget_le_power (n : ℕ) {U ζ : ℝ}
    (hU : 1 ≤ U) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    localizedMajorArcLengthBudget n U ζ ≤
      majorArcLengthConstant n U / ζ ^ majorArcLengthExponent n := by
  have hp : 0 < ζ ^ majorArcBiasExponent n := pow_pos hζ _
  have hp1 : ζ ^ majorArcBiasExponent n ≤ 1 := pow_le_one₀ hζ.le hζ1
  have hone : (1 : ℝ) ≤ 1 / ζ ^ majorArcBiasExponent n := (le_div_iff₀ hp).mpr (by simpa)
  have hC := (majorArcLocalizationConstant_pos n hU).le
  rw [localizedMajorArcLengthBudget_eq, localizedMajorArcBudget_constant n hU hζ]
  have he (x : ℝ) : 256 * U ^ 6 * x * (2 * U ^ 2) ^ ((n + 1) * 2) =
      majorArcLocalizationConstant n U * x := by
    unfold majorArcLocalizationConstant
    ring
  rw [he]
  calc
    _ ≤ majorArcLocalizationConstant n U *
        (majorArcBiasConstant n U / ζ ^ majorArcBiasExponent n +
          1 / ζ ^ majorArcBiasExponent n) / ζ ^ 2 := by gcongr
    _ = _ := by
      simp only [majorArcLengthConstant, majorArcLengthExponent, pow_add]
      ring

theorem localizedMajorArcErrorBudget_constant (n : ℕ) {U ζ : ℝ}
    (hU : 1 ≤ U) (hζ : 0 < ζ) :
    localizedMajorArcErrorBudget n U ζ =
      majorArcErrorConstant n U / ζ ^ majorArcErrorExponent n := by
  rw [localizedMajorArcErrorBudget_eq, localizedMajorArcBudget_constant n hU hζ]
  change (majorArcBiasConstant n U / ζ ^ majorArcBiasExponent n) *
    (majorArcLocalizationConstant n U / ζ ^ 2) ^ (n + 1) = _
  simp only [majorArcErrorConstant, majorArcErrorExponent, div_pow, pow_add, pow_mul]
  ring

end Erdos3

end

section

namespace Erdos3

def majorArcCoverExponent (n j : ℕ) : ℕ :=
  majorArcBiasExponent n * j + majorArcErrorExponent n

noncomputable def majorArcCoverConstant (n j : ℕ) (U V : ℝ) : ℝ :=
  1 + (majorArcBiasConstant n U * U ^ (n + 1)) ^ j + V * majorArcErrorConstant n U

def majorArcSpectrumExponent (n j : ℕ) : ℕ := 4 * majorArcCoverExponent n j * j

noncomputable def majorArcSpectrumConstant (n j : ℕ) (U V : ℝ) : ℝ :=
  (195 * majorArcCoverConstant n j U V ^ 4) ^ j

theorem majorArcCoverConstant_one_le (n j : ℕ) {U V : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) : 1 ≤ majorArcCoverConstant n j U V := by
  have hq := (majorArcBiasConstant_pos n hU).le
  have he := (majorArcErrorConstant_pos n hU).le
  have hU0 : 0 ≤ U := le_trans (by norm_num) hU
  have hd : 0 ≤ (majorArcBiasConstant n U * U ^ (n + 1)) ^ j := by positivity
  unfold majorArcCoverConstant
  nlinarith only [hd, mul_nonneg hV he]

theorem majorArcSpectrumConstant_nonneg (n j : ℕ) (U V : ℝ) :
    0 ≤ majorArcSpectrumConstant n j U V := by
  unfold majorArcSpectrumConstant
  positivity

theorem majorArc_denominator_le_cover (n j : ℕ) {U V ζ : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    (localizedMajorArcBudget n U ζ * U ^ (n + 1)) ^ j ≤
      majorArcCoverConstant n j U V / ζ ^ majorArcCoverExponent n j := by
  have he := (majorArcErrorConstant_pos n hU).le
  have hC := (majorArcCoverConstant_one_le n j hU hV).trans' (by norm_num : (0 : ℝ) ≤ 1)
  have hle : (majorArcBiasConstant n U * U ^ (n + 1)) ^ j ≤
      majorArcCoverConstant n j U V := by
    unfold majorArcCoverConstant
    nlinarith only [mul_nonneg hV he]
  calc
    _ = (majorArcBiasConstant n U * U ^ (n + 1)) ^ j / ζ ^ (majorArcBiasExponent n * j) := by
      rw [localizedMajorArcBudget_constant n hU hζ, div_mul_eq_mul_div, div_pow, pow_mul]
    _ ≤ _ := inverse_power_mono hC hle hζ hζ1 (by unfold majorArcCoverExponent; omega)

theorem majorArc_scaled_error_le_cover (n j : ℕ) {U V ζ R P : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hscale : R / P ≤ V) :
    R * (localizedMajorArcErrorBudget n U ζ / P) ≤
      majorArcCoverConstant n j U V / ζ ^ majorArcCoverExponent n j := by
  have hE := (majorArcErrorConstant_pos n hU).le
  have hQ := (majorArcBiasConstant_pos n hU).le
  have hU0 : 0 ≤ U := le_trans (by norm_num) hU
  have hd : 0 ≤ (majorArcBiasConstant n U * U ^ (n + 1)) ^ j := by positivity
  have hC : 0 ≤ majorArcCoverConstant n j U V :=
    le_trans (by norm_num) (majorArcCoverConstant_one_le n j hU hV)
  have hle : V * majorArcErrorConstant n U ≤ majorArcCoverConstant n j U V := by
    unfold majorArcCoverConstant
    linarith only [hd]
  rw [localizedMajorArcErrorBudget_constant n hU hζ]
  calc
    _ = (R / P) * (majorArcErrorConstant n U / ζ ^ majorArcErrorExponent n) := by ring
    _ ≤ V * (majorArcErrorConstant n U / ζ ^ majorArcErrorExponent n) :=
      mul_le_mul_of_nonneg_right hscale (by positivity)
    _ = (V * majorArcErrorConstant n U) / ζ ^ majorArcErrorExponent n := by ring
    _ ≤ _ := inverse_power_mono hC hle hζ hζ1 (by unfold majorArcCoverExponent; omega)

theorem uniformMajorArcCover_card (J : Type*) [Fintype J] [DecidableEq J]
    (M n : ℕ) {U V ζ : ℝ} (hU : 1 ≤ U) (hV : 0 ≤ V) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    ((polynomialGridCover J M (majorArcCoverConstant n (Fintype.card J) U V)
      (majorArcCoverExponent n (Fintype.card J)) ζ).card : ℝ) ≤
      majorArcSpectrumConstant n (Fintype.card J) U V /
        ζ ^ majorArcSpectrumExponent n (Fintype.card J) :=
  polynomialGridCover_card J M _ (majorArcCoverConstant_one_le n _ hU hV) hζ hζ1

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def uniformSpectrumBlockCount (n j t : ℕ) : ℕ :=
  max (majorArcSpectrumExponent n j) (majorArcLengthExponent n * t) + 1

noncomputable def uniformBlockSpectrumCover (J : Type*) [Fintype J] [DecidableEq J]
    (M n : ℕ) (U V L ζ : ℝ) : Finset (J → Fin M) :=
  lengthAwareSpectrumCover (majorArcLengthConstant n U) L (majorArcLengthExponent n)
    (polynomialGridCover J M (majorArcCoverConstant n (Fintype.card J) U V)
      (majorArcCoverExponent n (Fintype.card J))) ζ

noncomputable def uniformBlockSpectrumCardBudget (n j t : ℕ) (U V W ζ : ℝ) : ℝ :=
  majorArcSpectrumConstant n j U V / ζ ^ majorArcSpectrumExponent n j +
    W * majorArcLengthConstant n U ^ t / ζ ^ (majorArcLengthExponent n * t)

noncomputable def uniformBlockSpectrumAccuracyConstant (n j t : ℕ) (U V W : ℝ) : ℝ :=
  2 * majorArcSpectrumConstant n j U V * 2 ^ majorArcSpectrumExponent n j +
    W * (2 ^ majorArcLengthExponent n * majorArcLengthConstant n U) ^ t

theorem uniformBlockSpectrumCover_card (J : Type*) [Fintype J] [DecidableEq J]
    (M n t : ℕ) {U V W L ζ : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t) :
    ((uniformBlockSpectrumCover J M n U V L ζ).card : ℝ) ≤
      uniformBlockSpectrumCardBudget n (Fintype.card J) t U V W ζ := by
  apply lengthAwareSpectrumCover_card _ hL hW (majorArcSpectrumConstant_nonneg _ _ _ _)
    (majorArcLengthConstant_pos n hU).le hζ
  · simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using hsize
  · exact uniformMajorArcCover_card J M n hU hV hζ hζ1

theorem uniformBlockSpectrum_tail {B J : Type*} [Fintype B] [Fintype J] [DecidableEq J]
    (M n t : ℕ) (coeff : B → (J → Fin M) → ℂ) {U V W L ζ ε : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hε : 0 ≤ ε)
    (hB : uniformSpectrumBlockCount n (Fintype.card J) t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t)
    (hminor : ∀ δ, 0 < δ → δ ≤ 1 → majorArcLengthConstant n U / δ ^ majorArcLengthExponent n ≤ L →
      ∀ b k, k ∉ polynomialGridCover J M (majorArcCoverConstant n (Fintype.card J) U V)
        (majorArcCoverExponent n (Fintype.card J)) δ → ‖coeff b k‖ ≤ δ)
    (haccuracy : uniformBlockSpectrumAccuracyConstant n (Fintype.card J) t U V W * ζ ≤ ε) :
    spectrumTail (uniformBlockSpectrumCover J M n U V L ζ) (fun k => ‖∏ b, coeff b k‖) ≤ ε := by
  classical
  apply lengthAwareSpectrumCover_accuracy coeff _ (t := t)
    (a := majorArcSpectrumExponent n (Fintype.card J))
    (majorArcLengthConstant_pos n hU) hL hW
    (majorArcSpectrumConstant_nonneg n (Fintype.card J) U V) hζ hζ1 hε
  · unfold majorArcLengthExponent; omega
  · unfold uniformSpectrumBlockCount at hB; omega
  · unfold uniformSpectrumBlockCount at hB; omega
  · simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using hsize
  · intro δ hδ hδ1
    exact uniformMajorArcCover_card J M n hU hV hδ hδ1
  · exact hminor
  · exact haccuracy

theorem exists_uniformBlockSpectrum_level (n j t : ℕ) {U V W ε : ℝ}
    (hU : 1 ≤ U) (hW : 0 ≤ W) (hε : 0 < ε) :
    ∃ ζ : ℝ, 0 < ζ ∧ ζ ≤ 1 ∧ uniformBlockSpectrumAccuracyConstant n j t U V W * ζ ≤ ε := by
  have hC := (majorArcLengthConstant_pos n hU).le
  exact exists_spectrum_retained_level (majorArcSpectrumConstant_nonneg n j U V)
    (show 0 ≤ W * (2 ^ majorArcLengthExponent n * majorArcLengthConstant n U) ^ t by positivity)
    hε (majorArcSpectrumExponent n j)

end Erdos3

end

section

namespace Erdos3

theorem polynomialGridCover_character {J : Type*} [Fintype J] [DecidableEq J]
    {M : ℕ} (hM : 0 < M) {C ζ : ℝ} (r : ℕ) (hC : 1 ≤ C) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (k : J → Fin M) (hk : k ∈ polynomialGridCover J M C r ζ) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ (3 * C) ^ Fintype.card J / ζ ^ (r * Fintype.card J) ∧
      ∃ (a : J → ℤ) (ξ : J → ℝ), (∀ j, |ξ j| ≤ 2 * C / ζ ^ r) ∧
        ∀ j, ((k j).val : ℝ) / M = (a j : ℝ) / D + ξ j / M := by
  have hX := one_le_inverse_power hC hζ hζ1 r
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ C / ζ ^ r by linarith)
  obtain ⟨D, hD, hDQ, a, ξ, hξ, he⟩ := rationalGridMajorBox_character hM k hk
  refine ⟨D, hD, ?_, a, ξ, ?_, he⟩
  · have hq : (⌈C / ζ ^ r⌉₊ : ℝ) + 1 ≤ 3 * (C / ζ ^ r) := by linarith
    apply (hDQ.trans (pow_le_pow_left₀ (by positivity) hq _)).trans_eq
    rw [← mul_div_assoc, div_pow, pow_mul]
  · intro j
    have hh := hξ j
    have heq : 2 * C / ζ ^ r = 2 * (C / ζ ^ r) := by ring
    rw [heq]
    linarith

theorem fullGrid_rational_character {J : Type*} [Fintype J]
    {M : ℕ} (hM : 0 < M) {A : ℝ} (hA : 0 ≤ A)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ A) (k : J → Fin M) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ 1 + A ∧
      ∃ a : J → ℤ, ∀ j, ((k j).val : ℝ) / M = (a j : ℝ) / D := by
  classical
  by_cases hj : Fintype.card J = 0
  · let : IsEmpty J := Fintype.card_eq_zero_iff.mp hj
    exact ⟨1, by omega, by norm_num; linarith, fun _ => 0, fun j => isEmptyElim j⟩
  · have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hp : (M : ℝ) ≤ (M : ℝ) ^ Fintype.card J := by
      simpa only [pow_one] using pow_le_pow_right₀ hM1 (show 1 ≤ Fintype.card J by omega)
    refine ⟨M, hM, by linarith, fun j => (k j).val, ?_⟩
    intro j
    simp only [Int.cast_natCast]

noncomputable def uniformCharacterDenominatorBound (n j t : ℕ) (U V W ζ : ℝ) : ℝ :=
  1 + (3 * majorArcCoverConstant n j U V) ^ j / ζ ^ (majorArcCoverExponent n j * j) +
    W * majorArcLengthConstant n U ^ t / ζ ^ (majorArcLengthExponent n * t)

theorem uniformBlockSpectrumCover_character {J : Type*} [Fintype J] [DecidableEq J]
    {M : ℕ} (hM : 0 < M) (n t : ℕ) {U V W L ζ : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t)
    (k : J → Fin M) (hk : k ∈ uniformBlockSpectrumCover J M n U V L ζ) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ uniformCharacterDenominatorBound n (Fintype.card J) t U V W ζ ∧
      ∃ (a : J → ℤ) (ξ : J → ℝ),
        (∀ j, |ξ j| ≤ 2 * majorArcCoverConstant n (Fintype.card J) U V / ζ ^ majorArcCoverExponent n (Fintype.card J)) ∧
        ∀ j, ((k j).val : ℝ) / M = (a j : ℝ) / D + ξ j / M := by
  classical
  have hC := majorArcCoverConstant_one_le n (Fintype.card J) hU hV
  have hCL := (majorArcLengthConstant_pos n hU).le
  by_cases hl : majorArcLengthConstant n U / ζ ^ majorArcLengthExponent n ≤ L
  · have hk' : k ∈ polynomialGridCover J M (majorArcCoverConstant n (Fintype.card J) U V)
        (majorArcCoverExponent n (Fintype.card J)) ζ := by
      simpa only [uniformBlockSpectrumCover, lengthAwareSpectrumCover, ite_eq_left hl] using hk
    obtain ⟨D, hD, hDb, a, ξ, hξ, he⟩ := polynomialGridCover_character hM _ hC hζ hζ1 k hk'
    refine ⟨D, hD, ?_, a, ξ, hξ, he⟩
    unfold uniformCharacterDenominatorBound
    have hs : 0 ≤ W * majorArcLengthConstant n U ^ t / ζ ^ (majorArcLengthExponent n * t) := by positivity
    linarith
  · have hb := length_small_grid_bound hW hL hsize (le_of_lt (lt_of_not_ge hl))
    obtain ⟨D, hD, hDb, a, ha⟩ := fullGrid_rational_character hM (by positivity) hb k
    refine ⟨D, hD, ?_, a, fun _ => 0, ?_, ?_⟩
    · unfold uniformCharacterDenominatorBound
      have hs : 0 ≤ (3 * majorArcCoverConstant n (Fintype.card J) U V) ^ Fintype.card J /
          ζ ^ (majorArcCoverExponent n (Fintype.card J) * Fintype.card J) := by positivity
      linarith
    · intro j
      simp only [abs_zero]
      positivity
    · intro j
      simpa only [zero_div, add_zero] using ha j

theorem grid_character_rescale {J : Type*} {R K D : ℕ} (hR : 0 < R)
    (k : J → Fin (R * K)) (a : J → ℤ) (ξ : J → ℝ) {H : ℝ}
    (hξ : ∀ j, |ξ j| ≤ H)
    (he : ∀ j, ((k j).val : ℝ) / (R * K) = (a j : ℝ) / D + ξ j / (R * K)) :
    ∃ ρ : J → ℝ, (∀ j, |ρ j| ≤ H) ∧
      ∀ j, ((k j).val : ℝ) / (R * K) = (a j : ℝ) / D + ρ j / K := by
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  refine ⟨fun j => ξ j / R, ?_, ?_⟩
  · intro j
    rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ R from Nat.cast_nonneg R)]
    exact (div_le_self (abs_nonneg _) hR1).trans (hξ j)
  · intro j
    simpa only [div_div] using he j

end Erdos3

end

section

namespace Erdos3

noncomputable def uniformScaledRetainedFrequencyBound (n d : ℕ) (U V ζ : ℝ) : ℝ :=
  (⌈majorArcCoverConstant n d U V / ζ ^ majorArcCoverExponent n d⌉₊ : ℝ)

noncomputable def uniformScaledRetainedDenominatorBound (n d t : ℕ) (U V W ζ : ℝ) : ℝ :=
  max ((uniformScaledRetainedFrequencyBound n d U V ζ + 1) ^ d)
    (W * majorArcLengthConstant n U ^ t / ζ ^ (majorArcLengthExponent n * t))

theorem uniformScaledRetainedFrequencyBound_nonneg (n d : ℕ) (U V ζ : ℝ) :
    0 ≤ uniformScaledRetainedFrequencyBound n d U V ζ := Nat.cast_nonneg _

theorem uniformScaledRetainedDenominatorBound_one_le (n d t : ℕ) (U V W ζ : ℝ) :
    1 ≤ uniformScaledRetainedDenominatorBound n d t U V W ζ := by
  apply (one_le_pow₀ (show 1 ≤ uniformScaledRetainedFrequencyBound n d U V ζ + 1 by
    linarith [uniformScaledRetainedFrequencyBound_nonneg n d U V ζ])).trans
  exact le_max_left _ _

theorem uniformBlockSpectrumCover_scaled_character {J : Type*} [Fintype J] [DecidableEq J]
    {K M : ℕ} (hK : 0 < K) (hKM : K ≤ M) (n t : ℕ) {U V W L ζ : ℝ}
    (hL : 0 ≤ L) (hW : 0 ≤ W)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t)
    (k : J → Fin M) (hk : k ∈ uniformBlockSpectrumCover J M n U V L ζ) :
    ∃ D : ℕ, 0 < D ∧
      (D : ℝ) ≤ uniformScaledRetainedDenominatorBound n (Fintype.card J) t U V W ζ ∧
      ∃ (a : J → ℤ) (ω : J → ℝ),
        (∀ j, |ω j| ≤ uniformScaledRetainedFrequencyBound n (Fintype.card J) U V ζ) ∧
        ∀ j, ((k j).val : ℝ) / M = (a j : ℝ) / D + ω j / K :=
  lengthAwarePolynomialGrid_character hK hKM hL hW hsize k hk

theorem uniformBlockSpectrumCover_modes {J : Type*} [Fintype J] [DecidableEq J]
    {K M : ℕ} (hK : 0 < K) (hKM : K ≤ M) (n t : ℕ) {U V W L ζ : ℝ}
    (hL : 0 ≤ L) (hW : 0 ≤ W)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t) :
    ∃ (D : (J → Fin M) → ℕ) (a : (J → Fin M) → J → ℤ) (ω : (J → Fin M) → J → ℝ),
      (∀ k, 0 < D k) ∧ ∀ k ∈ uniformBlockSpectrumCover J M n U V L ζ,
        (D k : ℝ) ≤ uniformScaledRetainedDenominatorBound n (Fintype.card J) t U V W ζ ∧
        (∀ j, |ω k j| ≤ uniformScaledRetainedFrequencyBound n (Fintype.card J) U V ζ) ∧
        ∀ j, ((k j).val : ℝ) / M = (a k j : ℝ) / D k + ω k j / K := by
  classical
  have hex (k : J → Fin M) : ∃ D : ℕ, 0 < D ∧ ∃ (a : J → ℤ) (ω : J → ℝ),
      k ∈ uniformBlockSpectrumCover J M n U V L ζ →
        (D : ℝ) ≤ uniformScaledRetainedDenominatorBound n (Fintype.card J) t U V W ζ ∧
        (∀ j, |ω j| ≤ uniformScaledRetainedFrequencyBound n (Fintype.card J) U V ζ) ∧
        ∀ j, ((k j).val : ℝ) / M = (a j : ℝ) / D + ω j / K := by
    by_cases hk : k ∈ uniformBlockSpectrumCover J M n U V L ζ
    · obtain ⟨D, hD, hb, a, ω, hω, he⟩ :=
        uniformBlockSpectrumCover_scaled_character hK hKM n t hL hW hsize k hk
      exact ⟨D, hD, a, ω, fun _ => ⟨hb, hω, he⟩⟩
    · exact ⟨1, Nat.zero_lt_one, 0, 0, fun h => (hk h).elim⟩
  choose D hD a ω h using hex
  exact ⟨D, a, ω, hD, h⟩

end Erdos3

end

end OAI
