import OAI.Combinatorics.Progressions.Estimates.FixedPositiveCoefficientSource
import OAI.Combinatorics.Progressions.Geometry.PrincipalCoefficientPositiveSupport

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem weightedPositiveModerateGridCoefficient_mem_polynomial {n : ℕ} {I : Type*}
    [Fintype I] [DecidableEq I] (c : NormalizedScalarCubeSource Empty)
    (s : Fin (n + 1) → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V ζ : ℝ}
    (hc : ScalarCubePrimitiveBudget c A U) (h : ∀ j, ScalarCubePrimitiveBudget (s j) A U)
    (hpositive : ∀ z, c.source.weight z ≠ 0 → (c.length : ℝ) / 4 ≤ (z none : ℝ))
    (hV : 0 ≤ V) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hlen : ∀ j, positiveModerateLengthConstant n U / ζ ^ positiveModerateLengthExponent n ≤
      (s j).length)
    {M : ℕ} (hM : 0 < M)
    (hscale : (M : ℝ) / ((c.length : ℝ) * ∏ j, ((s j).length : ℝ)) ≤ V)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (k : J → Fin M) (hk : ζ ≤ ‖weightedModerateGridCoefficient c s 0 M J k‖) :
    k ∈ polynomialGridCover J M (positiveModerateCoverConstant n J.card U V)
      (positiveModerateCoverExponent n J.card) ζ := by
  have hU := hc.one_le
  have hU0 : 0 ≤ U := (by norm_num : (0 : ℝ) ≤ 1).trans hU
  have hLc : 0 < (c.length : ℝ) := Nat.cast_pos.mpr c.length_pos
  have hP : 0 < ∏ j, ((s j).length : ℝ) :=
    Finset.prod_pos (fun j _ => Nat.cast_pos.mpr (s j).length_pos)
  have hlength := positiveModerateLengthBudget_bounds n hU hζ hζ1
  have hcover := positiveModerateCoverBudget_bounds n J.card hU hV hζ hζ1
  by_cases hlong : majorArcLengthConstant (n + 1) U / ζ ^ majorArcLengthExponent (n + 1) ≤
      (c.length : ℝ)
  · have hm : (c.modulus none : ℝ) ≤ U :=
      (by exact_mod_cast c.modulus_le none : (c.modulus none : ℝ) ≤ c.modulusBound).trans
        hc.modulus_le
    have hm1 : (1 : ℝ) ≤ c.modulus none := by exact_mod_cast c.modulus_pos none
    have hden : (c.length : ℝ) * ∏ j, ((s j).length : ℝ) ≤
        ((c.modulus none : ℝ) * c.length) * ∏ j, ((s j).length : ℝ) := by
      exact mul_le_mul_of_nonneg_right
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hm1 hLc.le) hP.le
    have hscale' : (M : ℝ) /
        (((c.modulus none : ℝ) * c.length) * ∏ j, ((s j).length : ℝ)) ≤ V :=
      (div_le_div_of_nonneg_left (Nat.cast_nonneg M) (mul_pos hLc hP) hden).trans hscale
    have hq := (localizedMajorArcBudget_pos (n + 1) hU hζ).le
    have hd : (localizedMajorArcBudget (n + 1) U ζ *
        ((c.modulus none : ℝ) * U ^ (n + 1))) ^ J.card ≤
        (localizedMajorArcBudget (n + 1) U ζ * U ^ (n + 1 + 1)) ^ J.card := by
      apply pow_le_pow_left₀ (by positivity)
      apply mul_le_mul_of_nonneg_left _ hq
      rw [pow_succ' U (n + 1)]
      exact mul_le_mul_of_nonneg_right hm (pow_nonneg hU0 _)
    apply weightedModerateGridCoefficient_mem_major c s A hA hc h hζ hζ1
      ((localizedMajorArcLengthBudget_le_power (n + 1) hU hζ hζ1).trans hlong)
      (fun j => (localizedMajorArcLengthBudget_le_power (n + 1) hU hζ hζ1).trans
        (hlength.2.trans (hlen j))) 0 hM J hJ
    · exact (hd.trans (majorArc_denominator_le_cover (n + 1) J.card hU hV hζ hζ1)).trans
        (hcover.2.1.trans (Nat.le_ceil _))
    · exact (majorArc_scaled_error_le_cover (n + 1) J.card hU hV hζ hζ1 hscale').trans
        (hcover.2.1.trans (Nat.le_ceil _))
    · exact hk
  · have hV4 : 0 ≤ 4 * V := by positivity
    have hbias : ζ ≤ ‖c.source.complexMean (fun z =>
        (FiniteProbabilityWeights.pi (fun j => (s j).source)).complexMean
          (fun x => CircleFourier.character (((z none : ℝ) *
            booleanBlockPhase (gridJetFrequency M J k) (fun j i => (x j i : ℝ)) : ℝ) :
              CircleFourier.Circle)))‖ := by
      simpa only [weightedModerateGridCoefficient, zero_add] using hk
    obtain ⟨D, hD, hDb, a, ha⟩ := weighted_positiveCoefficient_major_arc (T := (c.length : ℝ)) c.source
      (fun z => (z none : ℤ)) s A hA h hζ hζ1 (show 0 < (c.length : ℝ) / 4 by positivity)
      (fun z hz => ⟨hpositive z hz, by
        exact_mod_cast (Finset.mem_Ico.mp (z none).property).2.le⟩)
      (fun j => (localizedMajorArcLengthBudget_le_power n hU hζ hζ1).trans
        (hlength.1.trans (hlen j))) (gridJetFrequency M J k) J hJ hbias
    have hraw : 0 ≤ (localizedMajorArcBudget n U ζ * U ^ (n + 1)) ^ J.card := by
      have := (localizedMajorArcBudget_pos n hU hζ).le
      positivity
    have hupper : 0 ≤ majorArcLengthConstant (n + 1) U /
        ζ ^ majorArcLengthExponent (n + 1) := by
      have := (majorArcLengthConstant_pos (n + 1) hU).le
      positivity
    have hDQ : (D : ℝ) ≤ positiveModerateCoverConstant n J.card U V /
        ζ ^ positiveModerateCoverExponent n J.card := hDb.trans
      ((mul_le_mul (lt_of_not_ge hlong).le
        (majorArc_denominator_le_cover n J.card hU hV4 hζ hζ1) hraw hupper).trans
          hcover.2.2)
    have hscale' : (M : ℝ) / (((c.length : ℝ) / 4) * ∏ j, ((s j).length : ℝ)) ≤
        4 * V := by
      calc
        _ = 4 * ((M : ℝ) / ((c.length : ℝ) * ∏ j, ((s j).length : ℝ))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hscale (by norm_num)
    apply mem_rationalGridMajorBox hM k hD
      (by exact_mod_cast hDQ.trans (Nat.le_ceil _)) a
      (fun S => by simpa only [gridJetFrequency_apply] using ha S)
    exact (majorArc_scaled_error_le_cover n J.card hU hV4 hζ hζ1 hscale').trans
      (hcover.1.trans (Nat.le_ceil _))

theorem weightedPositiveModerateGridCoefficient_minor_polynomial {n : ℕ} {I : Type*}
    [Fintype I] [DecidableEq I] (c : NormalizedScalarCubeSource Empty)
    (s : Fin (n + 1) → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V ζ : ℝ}
    (hc : ScalarCubePrimitiveBudget c A U) (h : ∀ j, ScalarCubePrimitiveBudget (s j) A U)
    (hpositive : ∀ z, c.source.weight z ≠ 0 → (c.length : ℝ) / 4 ≤ (z none : ℝ))
    (hV : 0 ≤ V) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hlen : ∀ j, positiveModerateLengthConstant n U / ζ ^ positiveModerateLengthExponent n ≤
      (s j).length)
    {M : ℕ} (hM : 0 < M)
    (hscale : (M : ℝ) / ((c.length : ℝ) * ∏ j, ((s j).length : ℝ)) ≤ V)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (k : J → Fin M) (hk : k ∉ polynomialGridCover J M (positiveModerateCoverConstant n J.card U V)
      (positiveModerateCoverExponent n J.card) ζ) :
    ‖weightedModerateGridCoefficient c s 0 M J k‖ ≤ ζ := by
  exact le_of_lt (lt_of_not_ge (fun hh => hk
    (weightedPositiveModerateGridCoefficient_mem_polynomial c s A hA hc h hpositive
      hV hζ hζ1 hlen hM hscale J hJ k hh)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

def positiveModerateSpectrumExponent (n j : ℕ) : ℕ :=
  4 * positiveModerateCoverExponent n j * j

noncomputable def positiveModerateSpectrumConstant (n j : ℕ) (U V : ℝ) : ℝ :=
  (195 * positiveModerateCoverConstant n j U V ^ 4) ^ j

def positiveModerateSpectrumBlockCount (n j t : ℕ) : ℕ :=
  max (positiveModerateSpectrumExponent n j) (positiveModerateLengthExponent n * t) + 1

noncomputable def positiveModerateSpectrumCover (J : Type*) [Fintype J] [DecidableEq J]
    (M n : ℕ) (U V L ζ : ℝ) : Finset (J → Fin M) :=
  lengthAwareSpectrumCover (positiveModerateLengthConstant n U) L (positiveModerateLengthExponent n)
    (polynomialGridCover J M (positiveModerateCoverConstant n (Fintype.card J) U V)
      (positiveModerateCoverExponent n (Fintype.card J))) ζ

theorem positiveModerateSpectrumCover_card (J : Type*) [Fintype J] [DecidableEq J]
    (M n t : ℕ) {U V W L ζ : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t) :
    ((positiveModerateSpectrumCover J M n U V L ζ).card : ℝ) ≤
      positiveModerateSpectrumConstant n (Fintype.card J) U V /
        ζ ^ positiveModerateSpectrumExponent n (Fintype.card J) +
      W * positiveModerateLengthConstant n U ^ t / ζ ^ (positiveModerateLengthExponent n * t) := by
  apply lengthAwareSpectrumCover_card _ hL hW
    (show 0 ≤ positiveModerateSpectrumConstant n (Fintype.card J) U V by
      unfold positiveModerateSpectrumConstant; positivity)
    (positiveModerateLengthConstant_pos n hU).le hζ
  · simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using hsize
  · exact polynomialGridCover_card J M _ (positiveModerateCoverConstant_one_le n _ hU hV) hζ hζ1

theorem exists_positiveModerateSpectrum_level (n j t : ℕ) {U V W ε : ℝ}
    (hU : 1 ≤ U) (hW : 0 ≤ W) (hε : 0 < ε) :
    ∃ ζ : ℝ, 0 < ζ ∧ ζ ≤ 1 ∧
      (2 * positiveModerateSpectrumConstant n j U V * 2 ^ positiveModerateSpectrumExponent n j +
        W * (2 ^ positiveModerateLengthExponent n * positiveModerateLengthConstant n U) ^ t) * ζ ≤
          ε := by
  have hC := (positiveModerateLengthConstant_pos n hU).le
  exact exists_spectrum_retained_level
    (show 0 ≤ positiveModerateSpectrumConstant n j U V by
      unfold positiveModerateSpectrumConstant; positivity)
    (show 0 ≤ W * (2 ^ positiveModerateLengthExponent n * positiveModerateLengthConstant n U) ^ t by
      positivity) hε (positiveModerateSpectrumExponent n j)

theorem positiveModerateSpectrum_tail {B J : Type*} [Fintype B] [Fintype J] [DecidableEq J]
    (M n t : ℕ) (coeff : B → (J → Fin M) → ℂ) {U V W L ζ ε : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hε : 0 ≤ ε)
    (hB : positiveModerateSpectrumBlockCount n (Fintype.card J) t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t)
    (hminor : ∀ δ, 0 < δ → δ ≤ 1 →
      positiveModerateLengthConstant n U / δ ^ positiveModerateLengthExponent n ≤ L →
      ∀ b k, k ∉ polynomialGridCover J M (positiveModerateCoverConstant n (Fintype.card J) U V)
        (positiveModerateCoverExponent n (Fintype.card J)) δ → ‖coeff b k‖ ≤ δ)
    (haccuracy : (2 * positiveModerateSpectrumConstant n (Fintype.card J) U V *
        2 ^ positiveModerateSpectrumExponent n (Fintype.card J) +
      W * (2 ^ positiveModerateLengthExponent n * positiveModerateLengthConstant n U) ^ t) * ζ ≤ ε) :
    spectrumTail (positiveModerateSpectrumCover J M n U V L ζ) (fun k => ‖∏ b, coeff b k‖) ≤ ε := by
  apply lengthAwareSpectrumCover_accuracy coeff _ (t := t)
    (a := positiveModerateSpectrumExponent n (Fintype.card J))
    (positiveModerateLengthConstant_pos n hU) hL hW
    (show 0 ≤ positiveModerateSpectrumConstant n (Fintype.card J) U V by
      unfold positiveModerateSpectrumConstant; positivity) hζ hζ1 hε
    (positiveModerateLengthExponent_pos n)
  · unfold positiveModerateSpectrumBlockCount at hB; omega
  · unfold positiveModerateSpectrumBlockCount at hB; omega
  · simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using hsize
  · intro δ hδ hδ1
    exact polynomialGridCover_card J M _ (positiveModerateCoverConstant_one_le n _ hU hV) hδ hδ1
  · exact hminor
  · exact haccuracy

theorem weightedPositiveModerate_uniform_spectrum_tail {B I : Type*}
    [Fintype B] [Fintype I] [DecidableEq I] {n : ℕ}
    (c : B → NormalizedScalarCubeSource Empty)
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V W L ζ ε : ℝ} {t : ℕ}
    (hU : 1 ≤ U) (hc : ∀ b, ScalarCubePrimitiveBudget (c b) A U)
    (h : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U)
    (hpositive : ∀ b z, (c b).source.weight z ≠ 0 → ((c b).length : ℝ) / 4 ≤ (z none : ℝ))
    (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hε : 0 ≤ ε)
    (hlen : ∀ b j, L ≤ (s b j).length)
    {M : ℕ} (hM : 0 < M)
    (hscale : ∀ b, (M : ℝ) / (((c b).length : ℝ) * ∏ j, ((s b j).length : ℝ)) ≤ V)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hB : positiveModerateSpectrumBlockCount n J.card t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ J.card ≤ W * L ^ t)
    (haccuracy : (2 * positiveModerateSpectrumConstant n J.card U V *
        2 ^ positiveModerateSpectrumExponent n J.card +
      W * (2 ^ positiveModerateLengthExponent n * positiveModerateLengthConstant n U) ^ t) * ζ ≤ ε) :
    spectrumTail (positiveModerateSpectrumCover J M n U V L ζ)
      (fun k => ‖∏ b, weightedModerateGridCoefficient (c b) (s b) 0 M J k‖) ≤ ε := by
  refine positiveModerateSpectrum_tail M n t
    (fun b k => weightedModerateGridCoefficient (c b) (s b) 0 M J k) hU hV hW hL hζ hζ1 hε
    (by simpa only [Fintype.card_coe] using hB)
    (by simpa only [Fintype.card_coe] using hsize) ?_
    (by simpa only [Fintype.card_coe] using haccuracy)
  intro δ hδ hδ1 hstart b k hk
  apply weightedPositiveModerateGridCoefficient_minor_polynomial (c b) (s b) A hA
    (hc b) (h b) (hpositive b) hV hδ hδ1 (fun j => hstart.trans (hlen b j))
    hM (hscale b) J hJ k
  simpa only [Fintype.card_coe] using hk

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem weightedPositiveAffineModerate_uniform_spectrum_tail {B I : Type*}
    [Fintype B] [Fintype I] [DecidableEq I] {n : ℕ}
    (c : B → NormalizedScalarCubeSource Empty)
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V W L ζ ε : ℝ} {t : ℕ}
    (hU : 1 ≤ U) (hc : ∀ b, ScalarCubePrimitiveBudget (c b) A U)
    (h : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U)
    (u : B → Fin (n + 1) → Option I → ℝ) (v : B → Fin (n + 1) → Option I → ℕ)
    (hv : ∀ b j i, 0 < v b j i)
    (hstride : ∀ b j i, ((v b j i * (s b j).modulus i : ℕ) : ℝ) ≤ U)
    (hpositive : ∀ b z, (c b).source.weight z ≠ 0 → ((c b).length : ℝ) / 4 ≤ (z none : ℝ))
    (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hε : 0 ≤ ε)
    (hlen : ∀ b j, L ≤ (s b j).length)
    {M : ℕ} (hM : 0 < M)
    (hscale : ∀ b, (M : ℝ) / (((c b).length : ℝ) * ∏ j, ((s b j).length : ℝ)) ≤ V)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hB : positiveModerateSpectrumBlockCount n J.card t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ J.card ≤ W * L ^ t)
    (haccuracy : (2 * positiveModerateSpectrumConstant n J.card U V *
        2 ^ positiveModerateSpectrumExponent n J.card +
      W * (2 ^ positiveModerateLengthExponent n * positiveModerateLengthConstant n U) ^ t) * ζ ≤ ε) :
    spectrumTail (positiveModerateSpectrumCover J M n U V L ζ)
      (fun k => ‖∏ b, weightedAffineModerateGridCoefficient (c b) (s b) (u b) (v b) 0 M J k‖) ≤ ε := by
  refine positiveModerateSpectrum_tail M n t
    (fun b k => weightedAffineModerateGridCoefficient (c b) (s b) (u b) (v b) 0 M J k) hU hV hW hL hζ hζ1 hε
    (by simpa only [Fintype.card_coe] using hB)
    (by simpa only [Fintype.card_coe] using hsize) ?_
    (by simpa only [Fintype.card_coe] using haccuracy)
  intro δ hδ hδ1 hstart b k hk
  apply weightedPositiveAffineModerateGridCoefficient_minor_polynomial (c b) (s b) A hA
    (hc b) (h b) (u b) (v b) (hv b) (hstride b) (hpositive b) hV hδ hδ1 (fun j => hstart.trans (hlen b j))
    hM (hscale b) J hJ k
  simpa only [Fintype.card_coe] using hk

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def positiveModerateAccuracyScale (n j t : ℕ) (U V W : ℝ) : ℝ :=
  1 + (2 * positiveModerateSpectrumConstant n j U V * 2 ^ positiveModerateSpectrumExponent n j +
    W * (2 ^ positiveModerateLengthExponent n * positiveModerateLengthConstant n U) ^ t)

noncomputable def positiveModerateRetainedBias (n j t : ℕ) (U V W ε : ℝ) : ℝ :=
  ε / positiveModerateAccuracyScale n j t U V W

theorem positiveModerateAccuracyScale_one_le (n j t : ℕ) {U V W : ℝ}
    (hU : 1 ≤ U) (hW : 0 ≤ W) :
    1 ≤ positiveModerateAccuracyScale n j t U V W := by
  have hL := (positiveModerateLengthConstant_pos n hU).le
  have hC : 0 ≤ positiveModerateSpectrumConstant n j U V := by
    unfold positiveModerateSpectrumConstant
    positivity
  unfold positiveModerateAccuracyScale
  exact le_add_of_nonneg_right (by positivity)

theorem positiveModerateRetainedBias_spec (n j t : ℕ) {U V W ε : ℝ}
    (hU : 1 ≤ U) (hW : 0 ≤ W) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 < positiveModerateRetainedBias n j t U V W ε ∧
    positiveModerateRetainedBias n j t U V W ε ≤ 1 ∧
    (2 * positiveModerateSpectrumConstant n j U V * 2 ^ positiveModerateSpectrumExponent n j +
      W * (2 ^ positiveModerateLengthExponent n * positiveModerateLengthConstant n U) ^ t) *
        positiveModerateRetainedBias n j t U V W ε ≤ ε := by
  have hD := positiveModerateAccuracyScale_one_le n j t (V := V) hU hW
  have hD0 : 0 < positiveModerateAccuracyScale n j t U V W := lt_of_lt_of_le zero_lt_one hD
  have hb : 0 < positiveModerateRetainedBias n j t U V W ε := div_pos hε hD0
  refine ⟨hb, (div_le_one hD0).mpr (hε1.trans hD), ?_⟩
  calc
    _ ≤ positiveModerateAccuracyScale n j t U V W *
        positiveModerateRetainedBias n j t U V W ε := by
      apply mul_le_mul_of_nonneg_right _ hb.le
      unfold positiveModerateAccuracyScale
      linarith
    _ = ε := by
      unfold positiveModerateRetainedBias
      field_simp

noncomputable def positiveModerateSpectrumCardBudget (n j t : ℕ) (U V W ε : ℝ) : ℝ :=
  positiveModerateSpectrumConstant n j U V /
      positiveModerateRetainedBias n j t U V W ε ^ positiveModerateSpectrumExponent n j +
    W * positiveModerateLengthConstant n U ^ t /
      positiveModerateRetainedBias n j t U V W ε ^ (positiveModerateLengthExponent n * t)

theorem positiveModerateSpectrumCover_card_budget (J : Type*) [Fintype J] [DecidableEq J]
    (M n t : ℕ) {U V W L ε : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t) :
    ((positiveModerateSpectrumCover J M n U V L
      (positiveModerateRetainedBias n (Fintype.card J) t U V W ε)).card : ℝ) ≤
        positiveModerateSpectrumCardBudget n (Fintype.card J) t U V W ε := by
  obtain ⟨hζ, hζ1, _⟩ := positiveModerateRetainedBias_spec n (Fintype.card J) t hU hW hε hε1
  exact positiveModerateSpectrumCover_card J M n t hU hV hW hL hζ hζ1 hsize

theorem positiveModerateSpectrum_absolute_cap {B J : Type*}
    [Fintype B] [Fintype J] [DecidableEq J]
    (M n t : ℕ) (coeff : B → (J → Fin M) → ℂ) {U V W L : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t)
    (hunit : ∀ b k, ‖coeff b k‖ ≤ 1)
    (htail : spectrumTail (positiveModerateSpectrumCover J M n U V L
      (positiveModerateRetainedBias n (Fintype.card J) t U V W 1))
        (fun k => ‖∏ b, coeff b k‖) ≤ 1) :
    (∑ k, ‖∏ b, coeff b k‖) ≤
      positiveModerateSpectrumCardBudget n (Fintype.card J) t U V W 1 + 1 := by
  exact (product_spectrum_absolute_cap coeff _ hunit).trans
    (add_le_add (positiveModerateSpectrumCover_card_budget J M n t hU hV hW hL
      zero_lt_one le_rfl hsize) htail)

theorem weightedPositiveModerateSpectrum_absolute_cap {B I : Type*}
    [Fintype B] [Fintype I] [DecidableEq I] {n : ℕ}
    (c : B → NormalizedScalarCubeSource Empty)
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (M t : ℕ) (J : Finset (Finset I)) {U V W L : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (hsize : (M : ℝ) ^ J.card ≤ W * L ^ t)
    (htail : spectrumTail (positiveModerateSpectrumCover J M n U V L
      (positiveModerateRetainedBias n J.card t U V W 1))
        (fun k => ‖∏ b, weightedModerateGridCoefficient (c b) (s b) 0 M J k‖) ≤ 1) :
    (∑ k, ‖∏ b, weightedModerateGridCoefficient (c b) (s b) 0 M J k‖) ≤
      positiveModerateSpectrumCardBudget n J.card t U V W 1 + 1 := by
  classical
  have hc := positiveModerateSpectrum_absolute_cap M n t
    (fun b k => weightedModerateGridCoefficient (c b) (s b) 0 M J k)
    hU hV hW hL (by simpa only [Fintype.card_coe] using hsize)
    (fun b k => weightedModerateGridCoefficient_norm_le_one (c b) (s b) 0 M J k)
    (by simpa only [Fintype.card_coe] using htail)
  simpa only [Fintype.card_coe] using hc

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem weightedAffineModerateGridCoefficient_norm_le_one {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I)
    (u : Fin n → Option I → ℝ) (v : Fin n → Option I → ℕ)
    (shift : ℝ) (M : ℕ) (J : Finset (Finset I)) (k : J → Fin M) :
    ‖weightedAffineModerateGridCoefficient c s u v shift M J k‖ ≤ 1 := by
  let p := FiniteProbabilityWeights.pi (fun j => (s j).source)
  apply (c.source.norm_complexMean_le_mean_norm _).trans
  apply (c.source.mean_mono (fun z => ?_)).trans_eq (c.source.mean_const 1)
  exact (p.norm_complexMean_le_mean_norm _).trans_eq (by
    simp only [CircleFourier.norm_character, p.mean_const])

theorem weightedPositiveAffineModerateSpectrum_absolute_cap {B I : Type*}
    [Fintype B] [Fintype I] [DecidableEq I] {n : ℕ}
    (c : B → NormalizedScalarCubeSource Empty)
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V W L : ℝ} {t : ℕ}
    (hU : 1 ≤ U) (hc : ∀ b, ScalarCubePrimitiveBudget (c b) A U)
    (h : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U)
    (u : B → Fin (n + 1) → Option I → ℝ) (v : B → Fin (n + 1) → Option I → ℕ)
    (hv : ∀ b j i, 0 < v b j i)
    (hstride : ∀ b j i, ((v b j i * (s b j).modulus i : ℕ) : ℝ) ≤ U)
    (hpositive : ∀ b z, (c b).source.weight z ≠ 0 → ((c b).length : ℝ) / 4 ≤ (z none : ℝ))
    (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (hlen : ∀ b j, L ≤ (s b j).length)
    {M : ℕ} (hM : 0 < M)
    (hscale : ∀ b, (M : ℝ) / (((c b).length : ℝ) * ∏ j, ((s b j).length : ℝ)) ≤ V)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hB : positiveModerateSpectrumBlockCount n J.card t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ J.card ≤ W * L ^ t)
 :
    (∑ k, ‖∏ b, weightedAffineModerateGridCoefficient (c b) (s b) (u b) (v b) 0 M J k‖) ≤
      positiveModerateSpectrumCardBudget n J.card t U V W 1 + 1 := by
  obtain ⟨hζ,hζ1,hacc⟩ := positiveModerateRetainedBias_spec n J.card t (V := V) hU hW
    (by norm_num : (0 : ℝ) < 1) le_rfl
  have ht := weightedPositiveAffineModerate_uniform_spectrum_tail c s A hA hU hc h u v hv hstride
    hpositive hV hW hL hζ hζ1 (by norm_num : (0 : ℝ) ≤ 1) hlen hM hscale J hJ hB hsize hacc
  have he := positiveModerateSpectrum_absolute_cap M n t
    (fun b k => weightedAffineModerateGridCoefficient (c b) (s b) (u b) (v b) 0 M J k)
    hU hV hW hL (by simpa only [Fintype.card_coe] using hsize)
    (fun b k => weightedAffineModerateGridCoefficient_norm_le_one (c b) (s b) (u b) (v b) 0 M J k)
    (by simpa only [Fintype.card_coe] using ht)
  simpa only [Fintype.card_coe] using he

end Erdos3

end

section

namespace Erdos3

noncomputable def positiveRetainedFrequencyBound (n d : ℕ) (U V ζ : ℝ) : ℝ :=
  (⌈positiveModerateCoverConstant n d U V / ζ ^ positiveModerateCoverExponent n d⌉₊ : ℝ)

noncomputable def positiveRetainedDenominatorBound (n d t : ℕ) (U V W ζ : ℝ) : ℝ :=
  max ((positiveRetainedFrequencyBound n d U V ζ + 1) ^ d)
    (W * positiveModerateLengthConstant n U ^ t / ζ ^ (positiveModerateLengthExponent n * t))

theorem positiveRetainedFrequencyBound_nonneg (n d : ℕ) (U V ζ : ℝ) :
    0 ≤ positiveRetainedFrequencyBound n d U V ζ := Nat.cast_nonneg _

theorem positiveRetainedDenominatorBound_one_le (n d t : ℕ) (U V W ζ : ℝ) :
    1 ≤ positiveRetainedDenominatorBound n d t U V W ζ := by
  apply (one_le_pow₀ (show 1 ≤ positiveRetainedFrequencyBound n d U V ζ + 1 by
    linarith [positiveRetainedFrequencyBound_nonneg n d U V ζ])).trans
  exact le_max_left _ _

theorem positiveModerateSpectrumCover_character {J : Type*} [Fintype J] [DecidableEq J]
    {K M : ℕ} (hK : 0 < K) (hKM : K ≤ M) (n t : ℕ) {U V W L ζ : ℝ}
    (hL : 0 ≤ L) (hW : 0 ≤ W)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t)
    (k : J → Fin M) (hk : k ∈ positiveModerateSpectrumCover J M n U V L ζ) :
    ∃ D : ℕ, 0 < D ∧
      (D : ℝ) ≤ positiveRetainedDenominatorBound n (Fintype.card J) t U V W ζ ∧
      ∃ (a : J → ℤ) (ω : J → ℝ),
        (∀ j, |ω j| ≤ positiveRetainedFrequencyBound n (Fintype.card J) U V ζ) ∧
        ∀ j, ((k j).val : ℝ) / M = (a j : ℝ) / D + ω j / K :=
  lengthAwarePolynomialGrid_character hK hKM hL hW hsize k hk

theorem positiveModerateSpectrumCover_modes {J : Type*} [Fintype J] [DecidableEq J]
    {K M : ℕ} (hK : 0 < K) (hKM : K ≤ M) (n t : ℕ) {U V W L ζ : ℝ}
    (hL : 0 ≤ L) (hW : 0 ≤ W)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t) :
    ∃ (D : (J → Fin M) → ℕ) (a : (J → Fin M) → J → ℤ) (ω : (J → Fin M) → J → ℝ),
      (∀ k, 0 < D k) ∧ ∀ k ∈ positiveModerateSpectrumCover J M n U V L ζ,
        (D k : ℝ) ≤ positiveRetainedDenominatorBound n (Fintype.card J) t U V W ζ ∧
        (∀ j, |ω k j| ≤ positiveRetainedFrequencyBound n (Fintype.card J) U V ζ) ∧
        ∀ j, ((k j).val : ℝ) / M = (a k j : ℝ) / D k + ω k j / K := by
  classical
  have hex (k : J → Fin M) : ∃ D : ℕ, 0 < D ∧ ∃ (a : J → ℤ) (ω : J → ℝ),
      k ∈ positiveModerateSpectrumCover J M n U V L ζ →
        (D : ℝ) ≤ positiveRetainedDenominatorBound n (Fintype.card J) t U V W ζ ∧
        (∀ j, |ω j| ≤ positiveRetainedFrequencyBound n (Fintype.card J) U V ζ) ∧
        ∀ j, ((k j).val : ℝ) / M = (a j : ℝ) / D + ω j / K := by
    by_cases hk : k ∈ positiveModerateSpectrumCover J M n U V L ζ
    · obtain ⟨D, hD, hb, a, ω, hω, he⟩ :=
        positiveModerateSpectrumCover_character hK hKM n t hL hW hsize k hk
      exact ⟨D, hD, a, ω, fun _ => ⟨hb, hω, he⟩⟩
    · exact ⟨1, Nat.zero_lt_one, 0, 0, fun h => (hk h).elim⟩
  choose D hD a ω h using hex
  exact ⟨D, a, ω, hD, h⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem positiveCoefficientSource_toNat_spec (c : NormalizedScalarCubeSource Empty)
    (hpositive : ∀ z, c.source.weight z ≠ 0 → (c.length : ℝ) / 4 ≤ (z none : ℝ))
    (z : IntegerScalarCubeBox Empty c.length) (hz : c.source.weight z ≠ 0) :
    0 < (z none : ℤ).toNat ∧ ((z none : ℤ).toNat : ℤ) = (z none : ℤ) ∧
      (z none : ℤ).toNat < c.length := by
  have hlen : (0 : ℝ) < c.length := by exact_mod_cast c.length_pos
  have hzR : (0 : ℝ) < (z none : ℝ) := lt_of_lt_of_le (by positivity) (hpositive z hz)
  have hzZ : (0 : ℤ) < (z none : ℤ) := by exact_mod_cast hzR
  have hupper := (Finset.mem_Ico.mp (z none).property).2
  exact ⟨by omega, Int.toNat_of_nonneg hzZ.le, by omega⟩

theorem positiveCoefficientSource_fixed_mixture (c : NormalizedScalarCubeSource Empty)
    (hpositive : ∀ z, c.source.weight z ≠ 0 → (c.length : ℝ) / 4 ≤ (z none : ℝ))
    (F : IntegerScalarCubeBox Empty c.length → ℤ → ℂ) :
    c.source.complexMean (fun z =>
      (fixedPositiveCoefficientSource (z none : ℤ).toNat).source.complexMean
        (fun x => F z (x none : ℤ))) =
      c.source.complexMean (fun z => F z (z none : ℤ)) := by
  simp_rw [fixedPositiveCoefficientSource_complexMean]
  unfold FiniteProbabilityWeights.complexMean
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : c.source.weight z = 0
  · simp only [hz, Complex.ofReal_zero, zero_mul]
  · dsimp only
    rw [(positiveCoefficientSource_toNat_spec c hpositive z hz).2.1]

theorem principalNormalizedSource_fixed_mixture {K T γ : ℝ}
    (hK : 0 < K) (hT : 0 < T) (hγ : 0 < γ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T))
    (F : IntegerScalarCubeBox Empty (principalNormalizedSource hK hT hγ hlarge).length →
      ℤ → ℂ) :
    (principalNormalizedSource hK hT hγ hlarge).source.complexMean (fun z =>
      (fixedPositiveCoefficientSource (z none : ℤ).toNat).source.complexMean
        (fun x => F z (x none : ℤ))) =
      (principalNormalizedSource hK hT hγ hlarge).source.complexMean
        (fun z => F z (z none : ℤ)) :=
  positiveCoefficientSource_fixed_mixture _
    (principalNormalizedSource_positive_support hK hT hγ hlarge) F

theorem positiveCoefficientSource_fixed_primitive (c : NormalizedScalarCubeSource Empty)
    {N : ℕ} (hshort : c.length ≤ N) (A : ℝ≥0)
    (z : IntegerScalarCubeBox Empty c.length) :
    ScalarCubePrimitiveBudget (fixedPositiveCoefficientSource (z none : ℤ).toNat) A
      (scalarCubePrimitiveEnvelope Empty A 1 0 (N + 1)) := by
  apply fixedPositiveCoefficientSource_primitive_of_le
  have hu := (Finset.mem_Ico.mp (z none).property).2
  omega

theorem positiveCoefficientSource_fixed_scale (c : NormalizedScalarCubeSource Empty)
    (hpositive : ∀ z, c.source.weight z ≠ 0 → (c.length : ℝ) / 4 ≤ (z none : ℝ))
    (z : IntegerScalarCubeBox Empty c.length) (hz : c.source.weight z ≠ 0)
    {M P V : ℝ} (hP : 0 < P) (hV : 0 ≤ V)
    (hscale : M / ((c.length : ℝ) * P) ≤ V) :
    M / (((fixedPositiveCoefficientSource (z none : ℤ).toNat).length : ℝ) * P) ≤
      4 * V := by
  have hlen : (0 : ℝ) < c.length := by exact_mod_cast c.length_pos
  have heZ := (positiveCoefficientSource_toNat_spec c hpositive z hz).2.1
  have heR : ((z none : ℤ).toNat : ℝ) = (z none : ℝ) := by exact_mod_cast heZ
  have hquarter := hpositive z hz
  have hlenle : (c.length : ℝ) ≤
      4 * ((fixedPositiveCoefficientSource (z none : ℤ).toNat).length : ℝ) := by
    simp only [fixedPositiveCoefficientSource_length, Nat.cast_add, Nat.cast_one]
    linarith
  have hscale' := (div_le_iff₀ (mul_pos hlen hP)).mp hscale
  apply (div_le_iff₀ (mul_pos (by exact_mod_cast
    (fixedPositiveCoefficientSource (z none : ℤ).toNat).length_pos) hP)).mpr
  have hbound := mul_le_mul_of_nonneg_left hlenle (mul_nonneg hV hP.le)
  nlinarith

theorem fixedPositiveCoefficientSource_gridCoefficient {I : Type*}
    [Fintype I] [DecidableEq I] {n : ℕ} (a : ℕ)
    (s : Fin n → NormalizedScalarCubeSource I) (shift : ℝ) (M : ℕ)
    (J : Finset (Finset I)) (k : J → Fin M) :
    weightedModerateGridCoefficient (fixedPositiveCoefficientSource a) s shift M J k =
      (FiniteProbabilityWeights.pi (fun j => (s j).source)).complexMean
        (fun x => CircleFourier.character
          (((shift + (a : ℝ)) * booleanBlockPhase (gridJetFrequency M J k)
            (fun j i => (x j i : ℝ)) : ℝ) : CircleFourier.Circle)) := by
  have he := fixedPositiveCoefficientSource_complexMean a
    (fun z => (FiniteProbabilityWeights.pi (fun j => (s j).source)).complexMean
      (fun x => CircleFourier.character
        (((shift + (z : ℝ)) * booleanBlockPhase (gridJetFrequency M J k)
          (fun j i => (x j i : ℝ)) : ℝ) : CircleFourier.Circle)))
  simpa only [weightedModerateGridCoefficient, Int.cast_natCast] using he

theorem fixedPositiveCoefficientSource_uniform_spectrum_tail
    {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I] {n N : ℕ}
    (c : B → NormalizedScalarCubeSource Empty)
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (z : ∀ b, IntegerScalarCubeBox Empty (c b).length)
    (hz : ∀ b, (c b).source.weight (z b) ≠ 0)
    (hpositive : ∀ b u, (c b).source.weight u ≠ 0 →
      ((c b).length : ℝ) / 4 ≤ (u none : ℝ))
    (hshort : ∀ b, (c b).length ≤ N)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V W L ζ ε : ℝ} {t : ℕ}
    (hU : 1 ≤ U) (hbudget : scalarCubePrimitiveEnvelope Empty A 1 0 (N + 1) ≤ U)
    (h : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U)
    (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hε : 0 ≤ ε)
    (hlen : ∀ b j, L ≤ (s b j).length)
    {M : ℕ} (hM : 0 < M)
    (hscale : ∀ b, (M : ℝ) / (((c b).length : ℝ) *
      ∏ j, ((s b j).length : ℝ)) ≤ V)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hB : positiveModerateSpectrumBlockCount n J.card t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ J.card ≤ W * L ^ t)
    (haccuracy : (2 * positiveModerateSpectrumConstant n J.card U (4 * V) *
        2 ^ positiveModerateSpectrumExponent n J.card +
      W * (2 ^ positiveModerateLengthExponent n * positiveModerateLengthConstant n U) ^ t) * ζ ≤ ε) :
    spectrumTail (positiveModerateSpectrumCover J M n U (4 * V) L ζ)
      (fun k => ‖∏ b, (FiniteProbabilityWeights.pi (fun j => (s b j).source)).complexMean
        (fun x => CircleFourier.character
          (((z b none : ℝ) * booleanBlockPhase (gridJetFrequency M J k)
            (fun j i => (x j i : ℝ)) : ℝ) : CircleFourier.Circle))‖) ≤ ε := by
  have hfixed := weightedPositiveModerate_uniform_spectrum_tail
    (fun b => fixedPositiveCoefficientSource (z b none : ℤ).toNat) s A hA hU
    (fun b => (positiveCoefficientSource_fixed_primitive (c b) (hshort b) A (z b)).mono hbudget)
    h (fun b u hu => fixedPositiveCoefficientSource_positive _
      (positiveCoefficientSource_toNat_spec (c b) (hpositive b) (z b) (hz b)).1 u hu)
    (show 0 ≤ 4 * V by positivity) hW hL hζ hζ1 hε hlen hM
    (fun b => positiveCoefficientSource_fixed_scale (c b) (hpositive b) (z b) (hz b)
      (Finset.prod_pos (fun j _ => by exact_mod_cast (s b j).length_pos)) hV (hscale b))
    J hJ hB hsize haccuracy
  have hvalue (b : B) : ((z b none : ℤ).toNat : ℝ) = (z b none : ℝ) := by
    exact_mod_cast (positiveCoefficientSource_toNat_spec (c b) (hpositive b) (z b) (hz b)).2.1
  simpa only [fixedPositiveCoefficientSource_gridCoefficient, zero_add, hvalue] using hfixed

end Erdos3

end

end OAI
