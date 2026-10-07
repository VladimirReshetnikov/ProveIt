import OAI.Combinatorics.Progressions.Probability.WeightedPlateauMixture

namespace OAI

section

namespace Erdos3

open scoped BigOperators

instance blockTorusFactor_neZero (q h b : ℕ) (A : ℝ) : NeZero (blockTorusFactor q h b A) :=
  ⟨(blockTorusFactor_pos q h b A).ne'⟩

theorem exists_scaled_grid_minimum {J : Type*} [Fintype J] [Nonempty J]
    (length : J → ℕ) (hpos : ∀ j, 0 < length j) {K R : ℕ} {E : ℝ} (p d : ℕ)
    (hpower : ∀ j, (K : ℝ) ≤ E * (length j : ℝ) ^ p) :
    ∃ m : ℕ, 0 < m ∧ (∀ j, m ≤ length j) ∧
      ((R * K : ℕ) : ℝ) ^ d ≤ ((R : ℝ) * E) ^ d * (m : ℝ) ^ (p * d) := by
  obtain ⟨m, hm, hmin, hKm⟩ := exists_minimum_side_power length hpos hpower
  refine ⟨m, hm, hmin, ?_⟩
  exact grid_size_power_bound (Nat.cast_nonneg R) (Nat.cast_nonneg (R * K))
    (by simp only [Nat.cast_mul, le_refl]) hKm

theorem weightedModerate_physical_volume_lower {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I)
    {K D : ℝ} (hD : 0 ≤ D) (hlower : K ≤ D * ((c.length : ℝ) * ∏ j, ((s j).length : ℝ))) :
    K ≤ D * (((c.modulus none : ℝ) * c.length) * ∏ j, ((s j).length : ℝ)) := by
  have hm : (1 : ℝ) ≤ c.modulus none := by exact_mod_cast c.modulus_pos none
  apply hlower.trans
  apply mul_le_mul_of_nonneg_left _ hD
  have hp : 0 ≤ (c.length : ℝ) * ∏ j, ((s j).length : ℝ) := by positivity
  have hh := mul_le_mul_of_nonneg_right hm hp
  simpa only [one_mul, mul_assoc] using hh

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem weightedCube_side_powers {B I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I) {K D T : ℝ} (hD : 0 ≤ D)
    (hlower : ∀ b, K ≤ D * ∏ j, ((s b j).length : ℝ))
    (hbalance : ∀ b i j, ((s b i).length : ℝ) ≤ T * (s b j).length) :
    ∀ b j, K ≤ (D * T ^ (n + 1)) * ((s b j).length : ℝ) ^ (n + 1) := by
  intro b j
  simpa only [Fintype.card_fin] using balanced_product_side_power
    (fun i => ((s b i).length : ℝ)) hD (fun i => Nat.cast_nonneg _) (hlower b) j
    (fun i => hbalance b i j)

theorem moderate_sliced_side_powers {A L K T x c : ℝ} {C D h : ℕ}
    (hA : 1 ≤ A) (hL : 1 ≤ L) (hD : 0 < D) (hh : 0 < h)
    (hscale : K ≤ L ^ C) (hrange : L ≤ A ^ D) (hcoefficient : A ^ h ≤ K / L ^ h)
    (hx : L ≤ T * x) (hc : K / L ^ h ≤ T * c) :
    K ≤ T ^ (D * C) * x ^ (D * C) ∧ K ≤ T ^ (D * C) * c ^ (D * C) := by
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  have hcoef0 : 0 ≤ K / L ^ h := (pow_nonneg hA0 h).trans hcoefficient
  have hpower : C ≤ D * C := by nlinarith
  have hvec : K ≤ L ^ (D * C) := hscale.trans (pow_le_pow_right₀ hL hpower)
  have hcoef := moderate_coefficient_side_power hA hL0 hh hscale hrange hcoefficient
  constructor
  · simpa only [one_mul] using side_power_after_width_loss
      (by norm_num : (0 : ℝ) ≤ 1) hL0 (by simpa only [one_mul] using hvec) hx
  · simpa only [one_mul] using side_power_after_width_loss
      (by norm_num : (0 : ℝ) ≤ 1) hcoef0 (by simpa only [one_mul] using hcoef) hc

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

theorem blockJetScaleBound_buffer_le_double (q h b : ℕ) (hb : 0 < b) :
    blockJetScaleBound q h b 1 + 1 / 4 ≤ blockJetScaleBound q h b 2 := by
  have hn : 1 ≤ b * 2 ^ h * (q + 1) ^ h := Nat.succ_le_of_lt (by positivity)
  have hr : (1 : ℝ) ≤ (b : ℝ) * 2 ^ h * ((q + 1 : ℕ) : ℝ) ^ h := by exact_mod_cast hn
  unfold blockJetScaleBound
  linarith only [hr]

variable {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I]
variable {n K M : ℕ} [NeZero M]
variable (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)

noncomputable def weightedCubePlateauApproximation (K : ℕ) (H : ℝ)
    (rows : Finset (Finset I)) (shift z : rows → ℤ) (F : Finset (rows → Fin M)) : ℂ :=
  (normalizedSupportPlateau H (fun t => ((z t : ℝ) - shift t) / K) : ℂ) *
    weightedCubeGridApproximation s K M rows shift z F

omit [NeZero M] in
theorem weightedCubePMF_zero_off_scaled_support [DecidableEq B]
    {V : ℝ} (hV : 0 ≤ V)
    (hvol : ∀ b, (∏ v, ((s b v).length : ℝ)) ≤ V * K)
    (rows : Finset (Finset I)) (hrows : ∀ t ∈ rows, t.card ≤ n + 1)
    (shift z : rows → ℤ) (μ : PMF (rows → ℤ))
    (hμ : (weightedCubeIntegerSource s).toPMF.map (weightedCubeIntegerJetSum s rows shift) = μ)
    (hz : ¬∀ t, |(z t : ℝ) - shift t| ≤
      blockJetScaleBound (Fintype.card I) (n + 1) (Fintype.card B) V * K) : μ z = 0 := by
  rw [← hμ]
  apply pmf_map_zero_off_range
  rintro ⟨x, hx⟩
  apply hz
  intro t
  rw [← hx]
  exact weightedCubeIntegerJetSum_scale_bound s hV (Nat.cast_nonneg K)
    hvol rows hrows shift x t

theorem weightedCubePlateauApproximation_error [DecidableEq B]
    {V : ℝ} (hV : 0 ≤ V) (hK : 0 < K)
    (hvol : ∀ b, (∏ v, ((s b v).length : ℝ)) ≤ V * K)
    (rows : Finset (Finset I)) (hrows : ∀ t ∈ rows, t.card ≤ n + 1)
    (shift z : rows → ℤ) (μ : PMF (rows → ℤ))
    (hμ : (weightedCubeIntegerSource s).toPMF.map (weightedCubeIntegerJetSum s rows shift) = μ)
    (F : Finset (rows → Fin M)) {ε : ℝ} (hε : 0 ≤ ε)
    (he : (∀ t, |(z t : ℝ) - shift t| ≤
        (blockJetScaleBound (Fintype.card I) (n + 1) (Fintype.card B) V + 1 / 4) * K) →
      ‖(((K : ℝ) ^ rows.card * (μ z).toReal : ℝ) : ℂ) -
        weightedCubeGridApproximation s K M rows shift z F‖ ≤ ε) :
    ‖(((K : ℝ) ^ rows.card * (μ z).toReal : ℝ) : ℂ) -
      weightedCubePlateauApproximation s K
        (blockJetScaleBound (Fintype.card I) (n + 1) (Fintype.card B) V) rows shift z F‖ ≤ ε := by
  let H := blockJetScaleBound (Fintype.card I) (n + 1) (Fintype.card B) V
  let χ := normalizedSupportPlateau H (fun t => ((z t : ℝ) - shift t) / K)
  let v : ℂ := ((K : ℝ) ^ rows.card * (μ z).toReal : ℝ)
  have hχ := normalizedSupportPlateau_range H (fun t => ((z t : ℝ) - shift t) / K)
  have hfix : (χ : ℂ) * v = v := by
    by_cases hz : ∀ t, |(z t : ℝ) - shift t| ≤ H * K
    · have hχ1 : χ = 1 := normalizedSupportPlateau_grid_one
        (blockJetScaleBound_nonneg _ _ _ hV) hK shift z hz
      simp only [hχ1, Complex.ofReal_one, one_mul]
    · have hzero := weightedCubePMF_zero_off_scaled_support s hV hvol rows hrows shift z μ hμ hz
      simp only [v, hzero, ENNReal.toReal_zero, mul_zero, Complex.ofReal_zero]
  change ‖v - (χ : ℂ) * weightedCubeGridApproximation s K M rows shift z F‖ ≤ ε
  by_cases hχ0 : χ = 0
  · have hv : v = 0 := by simpa only [hχ0, Complex.ofReal_zero, zero_mul] using hfix.symm
    simpa only [hv, hχ0, Complex.ofReal_zero, zero_mul, sub_self, norm_zero] using hε
  · have hv := he (normalizedSupportPlateau_grid_support hK shift z hχ0)
    calc
      _ = ‖(χ : ℂ) * (v - weightedCubeGridApproximation s K M rows shift z F)‖ := by
        rw [mul_sub, hfix]
      _ = χ * ‖v - weightedCubeGridApproximation s K M rows shift z F‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hχ.1]
      _ ≤ 1 * ε := mul_le_mul hχ.2 hv (norm_nonneg _) zero_le_one
      _ = ε := one_mul ε

theorem weightedCubePlateauApproximation_norm_le (H : ℝ)
    (rows : Finset (Finset I)) (shift z : rows → ℤ) (F : Finset (rows → Fin M)) {C : ℝ}
    (hscale : ((K : ℝ) / M) ^ rows.card ≤ 1)
    (hcap : (∑ k, ‖∏ b, weightedCubeGridCoefficient (s b) M rows k‖) ≤ C) :
    ‖weightedCubePlateauApproximation s K H rows shift z F‖ ≤ C := by
  have hC : 0 ≤ C := (Finset.sum_nonneg (fun _ _ => norm_nonneg _)).trans hcap
  have hsum : ‖∑ k ∈ F, (∏ b, weightedCubeGridCoefficient (s b) M rows k) *
      (rectangularGridCharacter M k shift * star (rectangularGridCharacter M k z))‖ ≤ C := by
    apply (norm_sum_le _ _).trans
    simp only [norm_mul, norm_star, rectangularGridCharacter_norm, mul_one]
    exact (Finset.sum_le_univ_sum_of_nonneg (fun _ => norm_nonneg _)).trans hcap
  have hχ := normalizedSupportPlateau_range H (fun t => ((z t : ℝ) - shift t) / K)
  unfold weightedCubePlateauApproximation weightedCubeGridApproximation
  rw [norm_mul, norm_mul, norm_pow, norm_div, Complex.norm_natCast, Complex.norm_natCast,
    Complex.norm_real, Real.norm_of_nonneg hχ.1]
  exact (mul_le_mul hχ.2 (mul_le_mul hscale hsum (norm_nonneg _) zero_le_one)
    (by positivity) zero_le_one).trans_eq (by simp)

theorem weightedCubePlateauApproximation_split
    (hK : 0 < K) (H : ℝ) (rows : Finset (Finset I)) (shift z : rows → ℤ)
    (F : Finset (rows → Fin M)) (D : (rows → Fin M) → ℕ) [∀ k, NeZero (D k)]
    (a : (rows → Fin M) → rows → ℤ) (ω : (rows → Fin M) → rows → ℝ)
    (hfreq : ∀ k ∈ F, ∀ t, ((k t).val : ℝ) / M = (a k t : ℝ) / D k + ω k t / K) :
    weightedCubePlateauApproximation s K H rows shift z F =
      ((K : ℂ) / M) ^ rows.card * ∑ k ∈ F,
        (∏ b, weightedCubeGridCoefficient (s b) M rows k) *
          (rationalGridPhase (D k) (a k) (integerGridResidue (D k) (shift - z)) *
            plateauFourierMode H (fun t => -ω k t) (fun t => ((z t : ℝ) - shift t) / K)) := by
  unfold weightedCubePlateauApproximation weightedCubeGridApproximation
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← plateau_grid_character_split H hK k (a k) (ω k) (hfreq k hk) shift z]
  ring

theorem weightedCubePlateauMixture_expansion
    {T : Type*} [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]
    (p : PMF T) (hK : 0 < K) (H : ℝ) (rows : Finset (Finset I))
    (shift : T → rows → ℤ) (z : rows → ℤ)
    (F : Finset (rows → Fin M)) (D : (rows → Fin M) → ℕ) [∀ k, NeZero (D k)]
    (a : (rows → Fin M) → rows → ℤ) (ω : (rows → Fin M) → rows → ℝ)
    (hfreq : ∀ k ∈ F, ∀ t, ((k t).val : ℝ) / M = (a k t : ℝ) / D k + ω k t / K) :
    (∫ v, weightedCubePlateauApproximation s K H rows (shift v) z F ∂p.toMeasure) =
      ((K : ℂ) / M) ^ rows.card * ∑ k ∈ F,
        (∏ b, weightedCubeGridCoefficient (s b) M rows k) *
          (star (rationalGridPhase (D k) (a k) (integerGridResidue (D k) z)) *
            plateauModeMixture p H (D k) K (a k) (ω k) shift (fun t => (z t : ℝ) / K)) := by
  simp_rw [weightedCubePlateauApproximation_split s hK H rows _ z F D a ω hfreq]
  rw [integral_const_mul, integral_finsetSum]
  · congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_const_mul, plateauModeMixture_grid_factor]
  · intro k _
    apply Integrable.const_mul
    apply pmf_integrable_of_norm_le p _ (B := 1)
    intro v
    rw [norm_mul, rationalGridPhase_norm, one_mul]
    exact plateauFourierMode_norm _ _ _

end Erdos3

end

end OAI
