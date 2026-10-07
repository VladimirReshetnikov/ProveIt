import OAI.Combinatorics.Progressions.Estimates.PMFLipschitzAverage
import OAI.Combinatorics.Progressions.Estimates.WeightedApproximationCaps
import OAI.Combinatorics.Progressions.Fourier.PlateauFourierMode
import OAI.Combinatorics.Progressions.Lattices.IntegerGridPlateauTransfer

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {T J : Type*} [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]
variable [Fintype J]

theorem rationalGridPhase_sub (D : ℕ) [NeZero D] (a u v : J → ℤ) :
    rationalGridPhase D a (integerGridResidue D (u - v)) =
      rationalGridPhase D a (integerGridResidue D u) *
        star (rationalGridPhase D a (integerGridResidue D v)) := by
  unfold rationalGridPhase integerGridResidue
  simp only [Pi.sub_apply, Int.cast_sub, mul_sub, Finset.sum_sub_distrib, map_sub]
  rw [sub_eq_add_neg, CircleFourier.character_add, CircleFourier.character_neg]

noncomputable def plateauModeMixture (p : PMF T) (H : ℝ) (D K : ℕ) [NeZero D]
    (a : J → ℤ) (ω : J → ℝ) (shift : T → J → ℤ) (x : J → ℝ) : ℂ :=
  ∫ t, rationalGridPhase D a (integerGridResidue D (shift t)) *
    plateauFourierMode H (fun j => -ω j) (x - fun j => (shift t j : ℝ) / K) ∂p.toMeasure

omit [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T] in
theorem plateauModeMixture_integrand_norm (H : ℝ) (D K : ℕ) [NeZero D]
    (a : J → ℤ) (ω : J → ℝ) (shift : T → J → ℤ) (x : J → ℝ) (t : T) :
    ‖rationalGridPhase D a (integerGridResidue D (shift t)) *
      plateauFourierMode H (fun j => -ω j) (x - fun j => (shift t j : ℝ) / K)‖ ≤ 1 := by
  rw [norm_mul, rationalGridPhase_norm, one_mul]
  exact plateauFourierMode_norm _ _ _

omit [Countable T] [MeasurableSingletonClass T] in
theorem plateauModeMixture_norm (p : PMF T) (H : ℝ) (D K : ℕ) [NeZero D]
    (a : J → ℤ) (ω : J → ℝ) (shift : T → J → ℤ) (x : J → ℝ) :
    ‖plateauModeMixture p H D K a ω shift x‖ ≤ 1 := by
  simpa only [plateauModeMixture, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const
      (ae_of_all p.toMeasure (plateauModeMixture_integrand_norm H D K a ω shift x))

theorem plateauModeMixture_lipschitz (p : PMF T) (H : ℝ) (D K : ℕ) [NeZero D]
    (a : J → ℤ) (ω : J → ℝ) (shift : T → J → ℤ) (W : ℝ≥0)
    (hW : ∀ j, |ω j| ≤ W) :
    LipschitzWith (CircleFourier.characterLipConstant * (Fintype.card J * W) + 4)
      (plateauModeMixture p H D K a ω shift) := by
  apply pmf_integral_lipschitz p _ _
    (fun t x => plateauModeMixture_integrand_norm H D K a ω shift x t)
  intro t
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, ← mul_sub, norm_mul, rationalGridPhase_norm, one_mul]
  have h := (plateauFourierMode_lipschitz H (fun j => -ω j) W
    (fun j => by simpa only [abs_neg] using hW j)).dist_le_mul
      (x - fun j => (shift t j : ℝ) / K) (y - fun j => (shift t j : ℝ) / K)
  have he : (x - fun j => (shift t j : ℝ) / K) -
      (y - fun j => (shift t j : ℝ) / K) = x - y := by abel
  simpa only [dist_eq_norm, he] using h

omit [Countable T] [MeasurableSingletonClass T] in
theorem plateauModeMixture_grid_factor (p : PMF T) (H : ℝ) (D K : ℕ) [NeZero D]
    (a : J → ℤ) (ω : J → ℝ) (shift : T → J → ℤ) (z : J → ℤ) :
    (∫ t, rationalGridPhase D a (integerGridResidue D (shift t - z)) *
      plateauFourierMode H (fun j => -ω j)
        (fun j => ((z j : ℝ) - shift t j) / K) ∂p.toMeasure) =
      star (rationalGridPhase D a (integerGridResidue D z)) *
        plateauModeMixture p H D K a ω shift (fun j => (z j : ℝ) / K) := by
  unfold plateauModeMixture
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun t => by
    have he : (fun j => ((z j : ℝ) - shift t j) / K) =
        (fun j => (z j : ℝ) / K) - (fun j => (shift t j : ℝ) / K) := by
      funext j
      exact sub_div _ _ _
    dsimp only
    rw [rationalGridPhase_sub, he]
    ring)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {B I : Type*} [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
variable {n K M : ℕ} [NeZero M]
variable (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
variable (offset : B → ℤ)

omit [DecidableEq B] in
noncomputable def weightedModeratePlateauApproximation (K : ℕ) (H : ℝ)
    (rows : Finset (Finset I)) (shift z : rows → ℤ) (F : Finset (rows → Fin M)) : ℂ :=
  (normalizedSupportPlateau H (fun t => ((z t : ℝ) - shift t) / K) : ℂ) *
    weightedModerateGridApproximation c s K M rows offset shift z F

omit [NeZero M] in
theorem weightedModerateGridDensity_eq_pmf_buffered
    {A : ℝ} (hA : 0 ≤ A) (hK : 0 < K)
    (hvol : ∀ b, (|(offset b : ℝ)| + (c b).length) *
      (∏ v, ((s b v).length : ℝ)) ≤ A * K)
    (hM : M = blockTorusFactor (Fintype.card I) n (Fintype.card B) A * K)
    (rows : Finset (Finset I)) (hrows : ∀ t ∈ rows, t.card ≤ n)
    (shift z : rows → ℤ) (μ : PMF (rows → ℤ))
    (hμ : (weightedModerateIntegerProductSource c s).toPMF.map
      (weightedModerateIntegerJetSum c s rows offset shift) = μ)
    (hz : ∀ t, |(z t : ℝ) - shift t| ≤
      (blockJetScaleBound (Fintype.card I) n (Fintype.card B) A + 1 / 4) * K) :
    integerGridDensity (weightedModerateIntegerProductSource c s)
      (weightedModerateIntegerJetSum c s rows offset shift) K M z =
        (K : ℝ) ^ rows.card * (μ z).toReal := by
  unfold integerGridDensity
  rw [hM, blockTorusFactor, integerGridMass_eq_imageMass_on_buffered_support
    (weightedModerateIntegerProductSource c s) (weightedModerateIntegerJetSum c s rows offset shift)
    shift z hK (fun x _ => weightedModerateIntegerJetSum_scale_bound c s offset hA
      (Nat.cast_nonneg K) hvol rows hrows shift x) hz,
    finiteImageMass_eq_toPMF, hμ, Fintype.card_coe]

theorem weightedModeratePointMass_error_plateau
    {A : ℝ} (hA : 0 ≤ A) (hK : 0 < K)
    (hvol : ∀ b, (|(offset b : ℝ)| + (c b).length) *
      (∏ v, ((s b v).length : ℝ)) ≤ A * K)
    (hM : M = blockTorusFactor (Fintype.card I) n (Fintype.card B) A * K)
    (rows : Finset (Finset I)) (hrows : ∀ t ∈ rows, t.card ≤ n)
    (shift z : rows → ℤ) (μ : PMF (rows → ℤ))
    (hμ : (weightedModerateIntegerProductSource c s).toPMF.map
      (weightedModerateIntegerJetSum c s rows offset shift) = μ)
    (F : Finset (rows → Fin M)) {ε : ℝ} (hε : 0 ≤ ε)
    (htail : spectrumTail F (fun k =>
      ‖∏ b, weightedModerateGridCoefficient (c b) (s b) (offset b : ℝ) M rows k‖) ≤ ε) :
    ‖(((K : ℝ) ^ rows.card * (μ z).toReal : ℝ) : ℂ) -
      weightedModeratePlateauApproximation c s offset K
        (blockJetScaleBound (Fintype.card I) n (Fintype.card B) A) rows shift z F‖ ≤ ε := by
  let H := blockJetScaleBound (Fintype.card I) n (Fintype.card B) A
  let χ := normalizedSupportPlateau H (fun t => ((z t : ℝ) - shift t) / K)
  let v : ℂ := ((K : ℝ) ^ rows.card * (μ z).toReal : ℝ)
  have hχ := normalizedSupportPlateau_range H (fun t => ((z t : ℝ) - shift t) / K)
  have hfix : (χ : ℂ) * v = v := by
    by_cases hz : ∀ t, |(z t : ℝ) - shift t| ≤ H * K
    · have hχ1 : χ = 1 := normalizedSupportPlateau_grid_one
        (blockJetScaleBound_nonneg _ _ _ hA) hK shift z hz
      simp only [hχ1, Complex.ofReal_one, one_mul]
    · have hz0 := weightedModeratePMF_zero_off_scaled_support c s offset hA hvol
        rows hrows shift z μ hμ hz
      simp only [v, hz0, ENNReal.toReal_zero, mul_zero, Complex.ofReal_zero]
  change ‖v - (χ : ℂ) * weightedModerateGridApproximation c s K M rows offset shift z F‖ ≤ ε
  by_cases hχ0 : χ = 0
  · have hv : v = 0 := by simpa only [hχ0, Complex.ofReal_zero, zero_mul] using hfix.symm
    simpa only [hv, hχ0, Complex.ofReal_zero, zero_mul, sub_self, norm_zero] using hε
  · have hz := normalizedSupportPlateau_grid_support hK shift z hχ0
    have hd := weightedModerateGridDensity_eq_pmf_buffered c s offset hA hK hvol hM
      rows hrows shift z μ hμ hz
    have he := weightedModerateGridDensity_error_of_tail c s K M rows offset F htail shift z
    rw [hd] at he
    have hscale : ((K : ℝ) / M) ^ rows.card ≤ 1 := by
      rw [hM, Nat.cast_mul]
      exact grid_scale_factor_le_one _ K rows.card (blockTorusFactor_pos _ _ _ _) hK
    have hv : ‖v - weightedModerateGridApproximation c s K M rows offset shift z F‖ ≤ ε :=
      he.trans (mul_le_of_le_one_left hε hscale)
    calc
      _ = ‖(χ : ℂ) * (v - weightedModerateGridApproximation c s K M rows offset shift z F)‖ := by
        rw [mul_sub, hfix]
      _ = χ * ‖v - weightedModerateGridApproximation c s K M rows offset shift z F‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hχ.1]
      _ ≤ 1 * ε := mul_le_mul hχ.2 hv (norm_nonneg _) zero_le_one
      _ = ε := one_mul ε

omit [DecidableEq B] in
theorem weightedModeratePlateauApproximation_norm_le_cap (H : ℝ)
    (rows : Finset (Finset I)) (shift z : rows → ℤ) (F : Finset (rows → Fin M)) {Q : ℝ}
    (hscale : ((K : ℝ) / M) ^ rows.card ≤ 1)
    (hQ : (∑ k, ‖∏ b, weightedModerateGridCoefficient (c b) (s b) (offset b : ℝ) M rows k‖) ≤ Q) :
    ‖weightedModeratePlateauApproximation c s offset K H rows shift z F‖ ≤ Q := by
  have hb := weightedModerateGridApproximation_norm_le_cap c s K M rows offset shift z F hscale hQ
  have hχ := normalizedSupportPlateau_range H (fun t => ((z t : ℝ) - shift t) / K)
  unfold weightedModeratePlateauApproximation
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hχ.1]
  exact (mul_le_mul_of_nonneg_left hb hχ.1).trans
    (mul_le_of_le_one_left ((norm_nonneg _).trans hb) hχ.2)

omit [DecidableEq B] in
theorem weightedModeratePlateauApproximation_split {D : ℕ} [NeZero D]
    (hK : 0 < K) (H : ℝ) (rows : Finset (Finset I)) (shift z : rows → ℤ)
    (F : Finset (rows → Fin M)) (a : (rows → Fin M) → rows → ℤ)
    (ω : (rows → Fin M) → rows → ℝ)
    (hfreq : ∀ k ∈ F, ∀ t, ((k t).val : ℝ) / M = (a k t : ℝ) / D + ω k t / K) :
    weightedModeratePlateauApproximation c s offset K H rows shift z F =
      ((K : ℂ) / M) ^ rows.card * ∑ k ∈ F,
        (∏ b, weightedModerateGridCoefficient (c b) (s b) (offset b : ℝ) M rows k) *
          (rationalGridPhase D (a k) (integerGridResidue D (shift - z)) *
            plateauFourierMode H (fun t => -ω k t) (fun t => ((z t : ℝ) - shift t) / K)) := by
  unfold weightedModeratePlateauApproximation weightedModerateGridApproximation
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← plateau_grid_character_split H hK k (a k) (ω k) (hfreq k hk) shift z]
  ring

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {B I T : Type*} [Fintype B] [Fintype I] [DecidableEq I]
variable [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]
variable {n K M : ℕ} [NeZero M]
variable (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
variable (offset : B → ℤ)

theorem weightedModeratePlateauApproximation_split_periods
    (hK : 0 < K) (H : ℝ) (rows : Finset (Finset I)) (shift z : rows → ℤ)
    (F : Finset (rows → Fin M)) (D : (rows → Fin M) → ℕ) [∀ k, NeZero (D k)]
    (a : (rows → Fin M) → rows → ℤ) (ω : (rows → Fin M) → rows → ℝ)
    (hfreq : ∀ k ∈ F, ∀ t, ((k t).val : ℝ) / M = (a k t : ℝ) / D k + ω k t / K) :
    weightedModeratePlateauApproximation c s offset K H rows shift z F =
      ((K : ℂ) / M) ^ rows.card * ∑ k ∈ F,
        (∏ b, weightedModerateGridCoefficient (c b) (s b) (offset b : ℝ) M rows k) *
          (rationalGridPhase (D k) (a k) (integerGridResidue (D k) (shift - z)) *
            plateauFourierMode H (fun t => -ω k t) (fun t => ((z t : ℝ) - shift t) / K)) := by
  unfold weightedModeratePlateauApproximation weightedModerateGridApproximation
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← plateau_grid_character_split H hK k (a k) (ω k) (hfreq k hk) shift z]
  ring

theorem weightedModeratePlateauMixture_expansion
    (p : PMF T) (hK : 0 < K) (H : ℝ) (rows : Finset (Finset I))
    (shift : T → rows → ℤ) (z : rows → ℤ)
    (F : Finset (rows → Fin M)) (D : (rows → Fin M) → ℕ) [∀ k, NeZero (D k)]
    (a : (rows → Fin M) → rows → ℤ) (ω : (rows → Fin M) → rows → ℝ)
    (hfreq : ∀ k ∈ F, ∀ t, ((k t).val : ℝ) / M = (a k t : ℝ) / D k + ω k t / K) :
    (∫ v, weightedModeratePlateauApproximation c s offset K H rows (shift v) z F ∂p.toMeasure) =
      ((K : ℂ) / M) ^ rows.card * ∑ k ∈ F,
        (∏ b, weightedModerateGridCoefficient (c b) (s b) (offset b : ℝ) M rows k) *
          (star (rationalGridPhase (D k) (a k) (integerGridResidue (D k) z)) *
            plateauModeMixture p H (D k) K (a k) (ω k) shift (fun t => (z t : ℝ) / K)) := by
  simp_rw [weightedModeratePlateauApproximation_split_periods c s offset hK H rows _ z F D a ω hfreq]
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
