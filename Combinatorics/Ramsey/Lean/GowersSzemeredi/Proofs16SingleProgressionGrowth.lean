import GowersSzemeredi.Proofs16CoherentAnchorGrowth
import GowersSzemeredi.Proofs16GlobalSingleProgression

/-! The parameters of `global_single_coherent_progression`, the current end of
the global chain, are triple-exponentially small.

Write `d = columnSpectrumCap (columnEightDensity alpha)` and
`T = exp(-2^(13^d)/2)`. The theorem's conclusion is stated with the core
density `z = globalEvenColumnZeroDensity alpha 4` and the derived parameters
`z^8/4`, `globalPopularAnchorTolerance alpha = z^16/20` and
`globalCoherentAnchorDensity alpha = z^16/4`, the rank
`globalEvenColumnModelRank alpha 4` and the radius
`globalEvenColumnZeroRadius alpha 4`.
`global_single_progression_parameters_le` collects the bounds: every
density parameter is at most `T`, the rank is at least `13^d`, and any `B`
with `exp(-B)` at most the radius is at least `13^d/2`. As before, these
bound the guaranteed parameters, not the actual sets. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A power `z^n/c` with `n ≥ 1` and `c ≥ 1` of a density `z ∈ (0,1]` stays
below `z`. -/
theorem pow_div_le_self {z c : Real} {n : Nat} (hz : 0 < z) (hz1 : z ≤ 1) (hn : n ≠ 0)
    (hc : 1 ≤ c) : z ^ n / c ≤ z := by
  have h1 : z ^ n ≤ z := pow_le_of_le_one hz.le hz1 hn
  have h2 : z ^ n / c ≤ z ^ n := div_le_self (by positivity) hc
  linarith

/-- **The parameters of the single coherent progression.** -/
theorem global_single_progression_parameters_le {alpha : Real} (ha : 0 < alpha)
    (ha1 : alpha ≤ 1) :
    let T := Real.exp (-(2 : Real) ^ (13 ^ columnSpectrumCap (columnEightDensity alpha)) / 2)
    globalEvenColumnZeroDensity alpha 4 ≤ T ∧
      (globalEvenColumnZeroDensity alpha 4) ^ 8 / 4 ≤ T ∧
      globalPopularAnchorTolerance alpha ≤ T ∧
      globalCoherentAnchorDensity alpha ≤ T ∧
      13 ^ columnSpectrumCap (columnEightDensity alpha) ≤ globalEvenColumnModelRank alpha 4 ∧
      ∀ B : Real, Real.exp (-B) ≤ globalEvenColumnZeroRadius alpha 4 →
        ((13 ^ columnSpectrumCap (columnEightDensity alpha) : Nat) : Real) / 2 ≤ B := by
  intro T
  have hz := globalEvenColumnZeroDensity_le_triple_exp ha ha1 (k := 4) (by norm_num)
  have hz0 := globalEvenColumnZeroDensity_pos (k := 4) ha ha1
  have hz1 := hz.trans (triple_exp_le_one _)
  refine ⟨hz, (pow_div_le_self hz0 hz1 (by norm_num) (by norm_num)).trans hz, ?_,
    globalCoherentAnchorDensity_le_triple_exp ha ha1,
    globalEvenColumnModelRank_ge ha ha1 (by norm_num),
    fun B hB => globalCoherentAnchorRadius_bound_ge ha ha1 hB⟩
  unfold globalPopularAnchorTolerance
  exact (pow_div_le_self hz0 hz1 (by norm_num) (by norm_num)).trans hz

end LeanProofs.GowersSzemeredi
