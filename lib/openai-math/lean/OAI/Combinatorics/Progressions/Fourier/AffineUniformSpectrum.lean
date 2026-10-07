import OAI.Combinatorics.Progressions.Lattices.AffineBlockScale

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem affine_weightedCube_uniform_spectrum {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I]
    {n : ℕ} (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (u : B → Fin (n + 1) → Option I → ℝ) (v : B → Fin (n + 1) → Option I → ℕ)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V W L ε : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L) (hε : 0 < ε)
    (h : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U) (hlen : ∀ b j, L ≤ (s b j).length)
    (hv : ∀ b j i, 0 < v b j i) (hstride : ∀ b j i, ((v b j i * (s b j).modulus i : ℕ) : ℝ) ≤ U)
    (M t : ℕ) (hM : 0 < M) (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hB : uniformSpectrumBlockCount n J.card t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ J.card ≤ W * L ^ t)
    (hscale : ∀ b, (M : ℝ) / ∏ j, ((s b j).length : ℝ) ≤ V) :
    let ζ := uniformBlockRetainedBias n J.card t U V W ε
    let S := uniformBlockSpectrumCover J M n U V L ζ
    spectrumTail S (fun k => ‖∏ b, affineWeightedCubeGridCoefficient (s b) (u b) (v b) M J k‖) ≤ ε ∧
      (∑ k, ‖∏ b, affineWeightedCubeGridCoefficient (s b) (u b) (v b) M J k‖) ≤
        uniformSpectrumAbsoluteCap n J.card t U V W := by
  let c b := affineWeightedCubeGridCoefficient (s b) (u b) (v b) M J
  have hminor : ∀ δ, 0 < δ → δ ≤ 1 → majorArcLengthConstant n U / δ ^ majorArcLengthExponent n ≤ L →
      ∀ b k, k ∉ polynomialGridCover J M (majorArcCoverConstant n (Fintype.card J) U V)
        (majorArcCoverExponent n (Fintype.card J)) δ → ‖c b k‖ ≤ δ := by
    intro δ hδ hδ1 hlength b k hk
    apply le_of_lt (lt_of_not_ge (fun hh => hk ?_))
    simpa only [Fintype.card_coe] using affineWeightedCubeGridCoefficient_mem_cover (s b) A hA (h b)
      hV hδ hδ1 (fun j => hlength.trans (hlen b j)) (u b) (v b) (hv b) (hstride b)
      hM (hscale b) J hJ k hh
  have hB' : uniformSpectrumBlockCount n (Fintype.card J) t ≤ Fintype.card B := by simpa only [Fintype.card_coe] using hB
  have hsize' : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t := by simpa only [Fintype.card_coe] using hsize
  obtain ⟨hζ, hζ1, hacc⟩ := uniformBlockRetainedBias_spec n (Fintype.card J) t hU hW hε
  constructor
  · simpa only [c, Fintype.card_coe] using uniformBlockSpectrum_tail M n t c hU hV hW hL
      hζ hζ1 hε.le hB' hsize' hminor hacc
  · simpa only [c, Fintype.card_coe] using uniformBlockSpectrum_absolute_cap M n t c hU hV hW hL
      hB' hsize' (fun b k => affineWeightedCubeGridCoefficient_norm_le_one (s b) (u b) (v b) M J k) hminor

theorem affine_weightedModerate_uniform_spectrum {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I]
    {n : ℕ} (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (shift : B → ℝ) (stride : B → ℕ) (u : B → Fin n → Option I → ℝ) (v : B → Fin n → Option I → ℕ)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V W L ε : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L) (hε : 0 < ε)
    (hc : ∀ b, ScalarCubePrimitiveBudget (c b) A U) (h : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U)
    (hclen : ∀ b, L ≤ (c b).length) (hlen : ∀ b j, L ≤ (s b j).length)
    (ht : ∀ b, 0 < stride b) (hv : ∀ b j i, 0 < v b j i)
    (hstride : ∀ b j i, ((v b j i * (s b j).modulus i : ℕ) : ℝ) ≤ U)
    (hcoeff : ∀ b, ((stride b * (c b).modulus none : ℕ) : ℝ) ≤ U)
    (M t : ℕ) (hM : 0 < M) (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n)
    (hB : uniformSpectrumBlockCount n J.card t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ J.card ≤ W * L ^ t)
    (hscale : ∀ b, (M : ℝ) / ((((stride b * (c b).modulus none : ℕ) : ℝ) * (c b).length) *
      ∏ j, ((s b j).length : ℝ)) ≤ V) :
    let ζ := uniformBlockRetainedBias n J.card t U V W ε
    let S := uniformBlockSpectrumCover J M n U V L ζ
    spectrumTail S (fun k => ‖∏ b, affineWeightedModerateGridCoefficient (c b) (s b) (shift b) (stride b) (u b) (v b) M J k‖) ≤ ε ∧
      (∑ k, ‖∏ b, affineWeightedModerateGridCoefficient (c b) (s b) (shift b) (stride b) (u b) (v b) M J k‖) ≤
        uniformSpectrumAbsoluteCap n J.card t U V W := by
  let f b := affineWeightedModerateGridCoefficient (c b) (s b) (shift b) (stride b) (u b) (v b) M J
  have hminor : ∀ δ, 0 < δ → δ ≤ 1 → majorArcLengthConstant n U / δ ^ majorArcLengthExponent n ≤ L →
      ∀ b k, k ∉ polynomialGridCover J M (majorArcCoverConstant n (Fintype.card J) U V)
        (majorArcCoverExponent n (Fintype.card J)) δ → ‖f b k‖ ≤ δ := by
    intro δ hδ hδ1 hlength b k hk
    apply le_of_lt (lt_of_not_ge (fun hh => hk ?_))
    simpa only [Fintype.card_coe] using affineWeightedModerateGridCoefficient_mem_cover (c b) (s b) A hA
      (hc b) (h b) hV hδ hδ1 (hlength.trans (hclen b)) (fun j => hlength.trans (hlen b j))
      (shift b) (stride b) (ht b) (u b) (v b) (hv b) (hstride b) (hcoeff b) hM (hscale b) J hJ k hh
  have hB' : uniformSpectrumBlockCount n (Fintype.card J) t ≤ Fintype.card B := by simpa only [Fintype.card_coe] using hB
  have hsize' : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t := by simpa only [Fintype.card_coe] using hsize
  obtain ⟨hζ, hζ1, hacc⟩ := uniformBlockRetainedBias_spec n (Fintype.card J) t hU hW hε
  constructor
  · simpa only [f, Fintype.card_coe] using uniformBlockSpectrum_tail M n t f hU hV hW hL
      hζ hζ1 hε.le hB' hsize' hminor hacc
  · simpa only [f, Fintype.card_coe] using uniformBlockSpectrum_absolute_cap M n t f hU hV hW hL hB' hsize'
      (fun b k => affineWeightedModerateGridCoefficient_norm_le_one (c b) (s b) (shift b) (stride b) (u b) (v b) M J k) hminor

end Erdos3

end

end OAI
