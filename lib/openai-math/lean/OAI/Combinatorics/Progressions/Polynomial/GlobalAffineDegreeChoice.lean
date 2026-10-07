import OAI.Combinatorics.Progressions.Lattices.InitialMaskedAffineComparison

namespace OAI

section

namespace Erdos3

noncomputable def affineGlobalComparisonDegree (A sourceDim siteDim : ℕ)
    (ε L T C shell modLog countLog : ℝ) : ℕ :=
  A + max (affineComparisonDegree sourceDim siteDim ε L T C shell modLog)
    (CyclicCrootSisask.spectralIterations shell
      ((A : ℝ) * ((sourceDim : ℝ) * modLog + (siteDim : ℝ) * modLog + 1) + 4 + countLog))

theorem affineGlobalComparisonDegree_bounds (A sourceDim siteDim : ℕ)
    (ε L T C shell modLog countLog : ℝ) (hcountLog : 0 ≤ countLog) :
    A + affineComparisonDegree sourceDim siteDim ε L T C shell modLog ≤
        affineGlobalComparisonDegree A sourceDim siteDim ε L T C shell modLog countLog ∧
    A + CyclicCrootSisask.spectralIterations shell
        ((A : ℝ) * ((sourceDim : ℝ) * modLog + (siteDim : ℝ) * modLog + 1) + 4) ≤
        affineGlobalComparisonDegree A sourceDim siteDim ε L T C shell modLog countLog ∧
    A + CyclicCrootSisask.spectralIterations shell
        ((A : ℝ) * ((sourceDim : ℝ) * modLog + (siteDim : ℝ) * modLog + 1) + 4 + countLog) ≤
        affineGlobalComparisonDegree A sourceDim siteDim ε L T C shell modLog countLog := by
  have hm := CyclicCrootSisask.spectralIterations_mono_budget (shell := shell)
    (show (A : ℝ) * ((sourceDim : ℝ) * modLog + (siteDim : ℝ) * modLog + 1) + 4 ≤
      (A : ℝ) * ((sourceDim : ℝ) * modLog + (siteDim : ℝ) * modLog + 1) + 4 + countLog by linarith)
  unfold affineGlobalComparisonDegree
  omega

theorem affineGlobalComparisonDegree_le (A sourceDim siteDim : ℕ)
    {ε L T C shell modLog countLog : ℝ}
    (hshell : 0 < shell) (hshell1 : shell ≤ 1) (hmodLog : 0 ≤ modLog) (hcountLog : 0 ≤ countLog) :
    (affineGlobalComparisonDegree A sourceDim siteDim ε L T C shell modLog countLog : ℝ) ≤
      (A : ℝ) + (affineComparisonDegree sourceDim siteDim ε L T C shell modLog : ℝ) +
        CyclicCrootSisask.spectralIterationFactor shell *
          ((A : ℝ) * ((sourceDim : ℝ) * modLog + (siteDim : ℝ) * modLog + 1) + 5 + countLog) := by
  have hbudget := CyclicCrootSisask.spectralIterations_le hshell hshell1
    (show 0 ≤ (A : ℝ) * ((sourceDim : ℝ) * modLog + (siteDim : ℝ) * modLog + 1) + 4 + countLog by positivity)
  have hnat : affineGlobalComparisonDegree A sourceDim siteDim ε L T C shell modLog countLog ≤
      A + affineComparisonDegree sourceDim siteDim ε L T C shell modLog +
        CyclicCrootSisask.spectralIterations shell
          ((A : ℝ) * ((sourceDim : ℝ) * modLog + (siteDim : ℝ) * modLog + 1) + 4 + countLog) := by
    unfold affineGlobalComparisonDegree
    omega
  have hreal : (affineGlobalComparisonDegree A sourceDim siteDim ε L T C shell modLog countLog : ℝ) ≤
      (A : ℝ) + (affineComparisonDegree sourceDim siteDim ε L T C shell modLog : ℝ) +
        (CyclicCrootSisask.spectralIterations shell
          ((A : ℝ) * ((sourceDim : ℝ) * modLog + (siteDim : ℝ) * modLog + 1) + 4 + countLog) : ℝ) := by
    exact_mod_cast hnat
  have heq : (A : ℝ) * ((sourceDim : ℝ) * modLog + (siteDim : ℝ) * modLog + 1) + 4 + countLog + 1 =
      (A : ℝ) * ((sourceDim : ℝ) * modLog + (siteDim : ℝ) * modLog + 1) + 5 + countLog := by ring
  rw [heq] at hbudget
  linarith

end Erdos3

end

end OAI
