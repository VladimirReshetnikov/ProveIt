import OAI.Combinatorics.Progressions.Probability.PerturbationCoefficientLaw

namespace OAI

section

namespace Erdos3

theorem integerAxisTail_width {V : Type*} (T : V → ℝ) (hT : ∀ v, 0 < T v)
    {K L s : ℕ} (hL : 0 < L) (hTL : ∀ v, T v ≤ L) {ε : ℝ} (hε : 0 < ε)
    (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L)
    (e : V →₀ ℕ) (he : e.sum (fun _ n => n) ≤ s) (ha : L ^ (s + 1) < K) :
    8 * (probabilityProfileLipschitz : ℝ) ≤ (ε / monomialScale T e) * K := by
  apply enormousPerturbation_large T hT (by exact_mod_cast hL) hε hTL
  · exact_mod_cast ha.le
  · exact hεL
  · exact he

noncomputable def integerAxisTailPMF {V : Type*} (T : V → ℝ) (hT : ∀ v, 0 < T v)
    (K L s : ℕ) (hK : 0 < K) (hL : 0 < L) (hTL : ∀ v, T v ≤ L) (ε : ℝ) (hε : 0 < ε)
    (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L)
    (e : V →₀ ℕ) (he : e.sum (fun _ n => n) ≤ s) : PMF ℤ :=
  if ha : L ^ (s + 1) < K then
    normalizedIntegerPMF K 0 (ε / monomialScale T e) (by exact_mod_cast hK)
      (div_pos hε (monomialScale_pos T hT e)) (integerAxisTail_width T hT hL hTL hε hεL e he ha)
  else PMF.pure 0

theorem integerAxisTailPMF_small {V : Type*} (T : V → ℝ) (hT : ∀ v, 0 < T v)
    {K L s : ℕ} (hK : 0 < K) (hL : 0 < L) (hTL : ∀ v, T v ≤ L) {ε : ℝ} (hε : 0 < ε)
    (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L)
    (e : V →₀ ℕ) (he : e.sum (fun _ n => n) ≤ s) (ha : K ≤ L ^ (s + 1)) :
    integerAxisTailPMF T hT K L s hK hL hTL ε hε hεL e he = PMF.pure 0 := by
  simp [integerAxisTailPMF, Nat.not_lt.mpr ha]

theorem integerAxisTailPMF_support {V : Type*} (T : V → ℝ) (hT : ∀ v, 0 < T v)
    {K L s : ℕ} (hK : 0 < K) (hL : 0 < L) (hTL : ∀ v, T v ≤ L) {ε : ℝ} (hε : 0 < ε)
    (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L)
    (e : V →₀ ℕ) (he : e.sum (fun _ n => n) ≤ s) {k : ℤ}
    (hk : k ∈ (integerAxisTailPMF T hT K L s hK hL hTL ε hε hεL e he).support) :
    |(k : ℝ) / K| * monomialScale T e < 3 * ε / 4 := by
  by_cases ha : L ^ (s + 1) < K
  · simp only [integerAxisTailPMF, ha, ↓reduceDIte] at hk
    exact integerPerturbation_scaled_support (by exact_mod_cast hK) hε
      (monomialScale_pos T hT e) (integerAxisTail_width T hT hL hTL hε hεL e he ha) hk
  · rw [integerAxisTailPMF_small T hT hK hL hTL hε hεL e he (Nat.le_of_not_gt ha)] at hk
    have hk0 : k = 0 := by simpa only [PMF.support_pure, Set.mem_singleton_iff] using hk
    subst k
    simp only [Int.cast_zero, zero_div, abs_zero, zero_mul]
    positivity

end Erdos3

end

end OAI
