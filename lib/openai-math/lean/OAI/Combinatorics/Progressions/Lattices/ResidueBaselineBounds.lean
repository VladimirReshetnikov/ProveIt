import OAI.Combinatorics.Progressions.Estimates.StableRetainedAtom

namespace OAI

section

namespace Erdos3

theorem residuePrimeCoordinateMean_re_le_one {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (g : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ)
    (M : ℕ) (a : σ → ℤ) (q : ι → ℕ) (K : Finset ι) (base : ∀ i, σ → ZMod (q i))
    (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1) :
    (residuePrimeCoordinateMean g lo N M a q K base).re ≤ 1 := by
  have ha : ∀ z ∈ translatedIntegerBox lo N, |(g z).re| ≤ 1 := by
    intro z hz
    rw [abs_of_nonneg (hg z hz).1]
    exact (hg z hz).2
  have h := residuePrimeCoordinateRealMean_bound (fun z => (g z).re) lo N M a q K base 1 zero_le_one ha
  rw [← residuePrimeCoordinateMean_re] at h
  exact (le_abs_self _).trans h

end Erdos3

end

end OAI
