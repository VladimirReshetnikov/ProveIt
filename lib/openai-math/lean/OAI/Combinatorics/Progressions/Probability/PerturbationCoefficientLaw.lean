import OAI.Combinatorics.Progressions.Lattices.IntegerRowInterpolationMixture

namespace OAI

section

namespace Erdos3

theorem affinePerturbation_scaled_support {ε S x : ℝ} (hε : 0 < ε) (hS : 0 < S)
    (hx : affineProbabilityProfile 0 (ε / S) x ≠ 0) : |x| * S < 3 * ε / 4 := by
  have hb := affineProbabilityProfile_support 0 (div_pos hε hS) hx
  simp only [sub_zero] at hb
  have he := mul_lt_mul_of_pos_right hb hS
  have hs : 3 * (ε / S) / 4 * S = 3 * ε / 4 := by field_simp
  rwa [hs] at he

theorem integerPerturbation_scaled_support {K ε S : ℝ} (hK : 0 < K) (hε : 0 < ε) (hS : 0 < S)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (ε / S) * K) {k : ℤ}
    (hk : k ∈ (normalizedIntegerPMF K 0 (ε / S) hK (div_pos hε hS) hlarge).support) :
    |(k : ℝ) / K| * S < 3 * ε / 4 := by
  have hb := normalizedIntegerPMF_support K 0 (ε / S) hK (div_pos hε hS) hlarge hk
  simp only [sub_zero] at hb
  have he := mul_lt_mul_of_pos_right hb hS
  have hs : 3 * (ε / S) / 4 * S = 3 * ε / 4 := by field_simp
  rwa [hs] at he

theorem enormousPerturbation_large {V : Type*} (T : V → ℝ) (hT : ∀ i, 0 < T i)
    {K L ε : ℝ} {s : ℕ} (hL : 1 ≤ L) (hε : 0 < ε) (hTL : ∀ i, T i ≤ L)
    (hK : L ^ (s + 1) ≤ K) (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L)
    (e : V →₀ ℕ) (he : e.sum (fun _ n => n) ≤ s) :
    8 * (probabilityProfileLipschitz : ℝ) ≤ (ε / monomialScale T e) * K := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hS := monomialScale_pos T hT e
  have hSL : L * monomialScale T e ≤ K := by
    calc
      _ ≤ L * L ^ s := mul_le_mul_of_nonneg_left
        (monomialScale_le_uniform_pow T (fun i => (hT i).le) hL hTL e he) hL0
      _ = L ^ (s + 1) := by rw [pow_succ]; ring
      _ ≤ K := hK
  have hb := mul_le_mul_of_nonneg_left hSL hε.le
  have hstep : ε * L ≤ (ε / monomialScale T e) * K := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hS).mpr
    nlinarith
  exact hεL.trans hstep

end Erdos3

end

end OAI
