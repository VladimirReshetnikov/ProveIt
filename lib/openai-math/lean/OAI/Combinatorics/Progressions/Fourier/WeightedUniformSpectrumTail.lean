import OAI.Combinatorics.Progressions.Fourier.UniformSpectrumAbsoluteCap

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem weightedCubeGridCoefficient_mem_polynomial {n : ℕ} {I : Type*}
    [Fintype I] [DecidableEq I] (s : Fin (n + 1) → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V ζ : ℝ}
    (h : ∀ j, ScalarCubePrimitiveBudget (s j) A U) (hV : 0 ≤ V)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hlen : ∀ j, majorArcLengthConstant n U / ζ ^ majorArcLengthExponent n ≤ (s j).length)
    {M : ℕ} (hM : 0 < M) (hscale : (M : ℝ) / ∏ j, ((s j).length : ℝ) ≤ V)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (k : J → Fin M) (hk : ζ ≤ ‖weightedCubeGridCoefficient s M J k‖) :
    k ∈ polynomialGridCover J M (majorArcCoverConstant n J.card U V)
      (majorArcCoverExponent n J.card) ζ := by
  have hU := (h 0).one_le
  apply weightedCubeGridCoefficient_mem_major s A hA h hζ hζ1
    (fun j => (localizedMajorArcLengthBudget_le_power n hU hζ hζ1).trans (hlen j)) hM J hJ
  · exact (majorArc_denominator_le_cover n J.card hU hV hζ hζ1).trans (Nat.le_ceil _)
  · exact (majorArc_scaled_error_le_cover n J.card hU hV hζ hζ1 hscale).trans (Nat.le_ceil _)
  · exact hk

theorem weightedCubeGridCoefficient_minor_polynomial {n : ℕ} {I : Type*}
    [Fintype I] [DecidableEq I] (s : Fin (n + 1) → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V ζ : ℝ}
    (h : ∀ j, ScalarCubePrimitiveBudget (s j) A U) (hV : 0 ≤ V)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hlen : ∀ j, majorArcLengthConstant n U / ζ ^ majorArcLengthExponent n ≤ (s j).length)
    {M : ℕ} (hM : 0 < M) (hscale : (M : ℝ) / ∏ j, ((s j).length : ℝ) ≤ V)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (k : J → Fin M) (hk : k ∉ polynomialGridCover J M (majorArcCoverConstant n J.card U V)
      (majorArcCoverExponent n J.card) ζ) : ‖weightedCubeGridCoefficient s M J k‖ ≤ ζ := by
  exact le_of_lt (lt_of_not_ge (fun hh => hk
    (weightedCubeGridCoefficient_mem_polynomial s A hA h hV hζ hζ1 hlen hM hscale J hJ k hh)))

theorem weightedModerateGridCoefficient_mem_polynomial {n : ℕ} {I : Type*}
    [Fintype I] [DecidableEq I] (c : NormalizedScalarCubeSource Empty)
    (s : Fin n → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V ζ : ℝ}
    (hc : ScalarCubePrimitiveBudget c A U) (h : ∀ j, ScalarCubePrimitiveBudget (s j) A U)
    (hV : 0 ≤ V) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hclen : majorArcLengthConstant n U / ζ ^ majorArcLengthExponent n ≤ c.length)
    (hlen : ∀ j, majorArcLengthConstant n U / ζ ^ majorArcLengthExponent n ≤ (s j).length)
    (shift : ℝ) {M : ℕ} (hM : 0 < M)
    (hscale : (M : ℝ) / (((c.modulus none : ℝ) * c.length) * ∏ j, ((s j).length : ℝ)) ≤ V)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n)
    (k : J → Fin M) (hk : ζ ≤ ‖weightedModerateGridCoefficient c s shift M J k‖) :
    k ∈ polynomialGridCover J M (majorArcCoverConstant n J.card U V)
      (majorArcCoverExponent n J.card) ζ := by
  have hU := hc.one_le
  have hU0 : 0 ≤ U := le_trans (by norm_num) hU
  have hm : (c.modulus none : ℝ) ≤ U :=
    (by exact_mod_cast c.modulus_le none : (c.modulus none : ℝ) ≤ c.modulusBound).trans hc.modulus_le
  have hq := (localizedMajorArcBudget_pos n hU hζ).le
  have hd : (localizedMajorArcBudget n U ζ * ((c.modulus none : ℝ) * U ^ n)) ^ J.card ≤
      (localizedMajorArcBudget n U ζ * U ^ (n + 1)) ^ J.card := by
    apply pow_le_pow_left₀ (by positivity)
    apply mul_le_mul_of_nonneg_left _ hq
    rw [pow_succ']
    exact mul_le_mul_of_nonneg_right hm (pow_nonneg hU0 n)
  apply weightedModerateGridCoefficient_mem_major c s A hA hc h hζ hζ1
    ((localizedMajorArcLengthBudget_le_power n hU hζ hζ1).trans hclen)
    (fun j => (localizedMajorArcLengthBudget_le_power n hU hζ hζ1).trans (hlen j)) shift hM J hJ
  · exact (hd.trans (majorArc_denominator_le_cover n J.card hU hV hζ hζ1)).trans (Nat.le_ceil _)
  · exact (majorArc_scaled_error_le_cover n J.card hU hV hζ hζ1 hscale).trans (Nat.le_ceil _)
  · exact hk

theorem weightedModerateGridCoefficient_minor_polynomial {n : ℕ} {I : Type*}
    [Fintype I] [DecidableEq I] (c : NormalizedScalarCubeSource Empty)
    (s : Fin n → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V ζ : ℝ}
    (hc : ScalarCubePrimitiveBudget c A U) (h : ∀ j, ScalarCubePrimitiveBudget (s j) A U)
    (hV : 0 ≤ V) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hclen : majorArcLengthConstant n U / ζ ^ majorArcLengthExponent n ≤ c.length)
    (hlen : ∀ j, majorArcLengthConstant n U / ζ ^ majorArcLengthExponent n ≤ (s j).length)
    (shift : ℝ) {M : ℕ} (hM : 0 < M)
    (hscale : (M : ℝ) / (((c.modulus none : ℝ) * c.length) * ∏ j, ((s j).length : ℝ)) ≤ V)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n)
    (k : J → Fin M) (hk : k ∉ polynomialGridCover J M (majorArcCoverConstant n J.card U V)
      (majorArcCoverExponent n J.card) ζ) : ‖weightedModerateGridCoefficient c s shift M J k‖ ≤ ζ := by
  exact le_of_lt (lt_of_not_ge (fun hh => hk
    (weightedModerateGridCoefficient_mem_polynomial c s A hA hc h hV hζ hζ1
      hclen hlen shift hM hscale J hJ k hh)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem weightedCube_uniform_spectrum_tail {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I]
    {n : ℕ} (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V W L ζ ε : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (h : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U)
    (hlen : ∀ b j, L ≤ (s b j).length)
    (M t : ℕ) (hM : 0 < M) (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hB : uniformSpectrumBlockCount n J.card t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ J.card ≤ W * L ^ t)
    (hscale : ∀ b, (M : ℝ) / ∏ j, ((s b j).length : ℝ) ≤ V)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hε : 0 ≤ ε)
    (haccuracy : uniformBlockSpectrumAccuracyConstant n J.card t U V W * ζ ≤ ε) :
    spectrumTail (uniformBlockSpectrumCover J M n U V L ζ)
      (fun k => ‖∏ b, weightedCubeGridCoefficient (s b) M J k‖) ≤ ε := by
  apply uniformBlockSpectrum_tail M n t (fun b => weightedCubeGridCoefficient (s b) M J)
    hU hV hW hL hζ hζ1 hε (by simpa only [Fintype.card_coe] using hB)
    (by simpa only [Fintype.card_coe] using hsize)
  · intro δ hδ hδ1 hlength b k hk
    exact weightedCubeGridCoefficient_minor_polynomial (s b) A hA (h b) hV hδ hδ1
      (fun j => hlength.trans (hlen b j)) hM (hscale b) J hJ k
      (by simpa only [Fintype.card_coe] using hk)
  · simpa only [Fintype.card_coe] using haccuracy

theorem weightedModerate_uniform_spectrum_tail {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I]
    {n : ℕ} (c : B → NormalizedScalarCubeSource Empty)
    (s : B → Fin n → NormalizedScalarCubeSource I) (shift : B → ℝ)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V W L ζ ε : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (hc : ∀ b, ScalarCubePrimitiveBudget (c b) A U)
    (h : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U)
    (hclen : ∀ b, L ≤ (c b).length) (hlen : ∀ b j, L ≤ (s b j).length)
    (M t : ℕ) (hM : 0 < M) (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n)
    (hB : uniformSpectrumBlockCount n J.card t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ J.card ≤ W * L ^ t)
    (hscale : ∀ b, (M : ℝ) / ((((c b).modulus none : ℝ) * (c b).length) *
      ∏ j, ((s b j).length : ℝ)) ≤ V)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hε : 0 ≤ ε)
    (haccuracy : uniformBlockSpectrumAccuracyConstant n J.card t U V W * ζ ≤ ε) :
    spectrumTail (uniformBlockSpectrumCover J M n U V L ζ)
      (fun k => ‖∏ b, weightedModerateGridCoefficient (c b) (s b) (shift b) M J k‖) ≤ ε := by
  apply uniformBlockSpectrum_tail M n t
    (fun b => weightedModerateGridCoefficient (c b) (s b) (shift b) M J)
    hU hV hW hL hζ hζ1 hε (by simpa only [Fintype.card_coe] using hB)
    (by simpa only [Fintype.card_coe] using hsize)
  · intro δ hδ hδ1 hlength b k hk
    exact weightedModerateGridCoefficient_minor_polynomial (c b) (s b) A hA (hc b) (h b)
      hV hδ hδ1 (hlength.trans (hclen b)) (fun j => hlength.trans (hlen b j)) (shift b)
      hM (hscale b) J hJ k (by simpa only [Fintype.card_coe] using hk)
  · simpa only [Fintype.card_coe] using haccuracy

end Erdos3

end

end OAI
