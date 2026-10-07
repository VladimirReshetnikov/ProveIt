import OAI.Combinatorics.Progressions.Lattices.AffineSampleAlphabet

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem residuePrimeCoordinateMean_congr_on_box {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (f g : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (hfg : ∀ z ∈ translatedIntegerBox lo N, f z = g z)
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    residuePrimeCoordinateMean f lo N M a q I x = residuePrimeCoordinateMean g lo N M a q I x := by
  classical
  unfold residuePrimeCoordinateMean
  apply Finset.expect_congr rfl
  intro z _
  apply hfg
  apply (mem_translatedIntegerBox lo N _).mpr
  intro j
  exact Finset.mem_Ico.mp (Finset.mem_filter.mp (z.val j).property).1

theorem ResiduePrimeCoordinateStable.congr_on_box {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    {f g : (σ → ℤ) → ℂ} {lo : σ → ℤ} {N : σ → ℕ} {M : ℕ} {a : σ → ℤ} {q : ι → ℕ}
    {r : ℕ} {δ : ℝ} {I : Finset ι} {x : ∀ i, σ → ZMod (q i)}
    (h : ResiduePrimeCoordinateStable f lo N M a q r δ I x)
    (hfg : ∀ z ∈ translatedIntegerBox lo N, f z = g z) :
    ResiduePrimeCoordinateStable g lo N M a q r δ I x := by
  intro J hIJ hJ y hxy hnonempty
  rw [← residuePrimeCoordinateMean_congr_on_box f g lo N M a q hfg I x,
    ← residuePrimeCoordinateMean_congr_on_box f g lo N M a q hfg (I ∪ J) y]
  exact h J hIJ hJ y hxy hnonempty

end Erdos3

end

end OAI
