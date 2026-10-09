import GowersSzemeredi.Proofs16ZeroCoreGrowth
import GowersSzemeredi.Proofs16GlobalCoherentAnchorParameters

/-! The even zero core and the global coherent anchors are triple-exponentially
sparse.

`global_coherent_column_anchors` starts from the even zero core at length
four. Its parameters `globalCoherentAnchorDensity`,
`globalCoherentAnchorTolerance` and `globalCoherentAnchorRank` inherit the
model-elimination losses quantified in `Proofs16ZeroCoreGrowth`. Write
`d = columnSpectrumCap (columnEightDensity alpha)`.
* `globalEvenColumnModelRank_ge`: the even model rank `⌈2k·d/δ⌉` is at
  least `13^d`, for every `k ≥ 1`.
* `globalEvenColumnZeroDensity_le_triple_exp`: the even zero-core density
  is at most `exp(-2^(13^d)/2)`. Its per-round divisor `5k` changes nothing.
* `globalCoherentAnchorDensity_le_triple_exp` and
  `globalCoherentAnchorTolerance_le_triple_exp`: so are the anchor density
  and tolerance; `globalCoherentAnchorRank_ge`: the anchor rank bound is
  at least `13^d`.
* `globalCoherentAnchorDensity_lt_polynomial_contract`: for `alpha ≤ 1/2`
  and `K ≤ 2^64` the anchor density is below `exp(-(4/alpha)^K)`.

As in `Proofs16ZeroCoreGrowth`, these bound the guaranteed parameters, not
the actual sets, and say nothing about other routes. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- **The even model rank is exponential in the spectrum cap.** -/
theorem globalEvenColumnModelRank_ge {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    {k : Nat} (hk : 1 ≤ k) :
    13 ^ columnSpectrumCap (columnEightDensity alpha) ≤ globalEvenColumnModelRank alpha k :=
  thirteen_pow_le_rank_ceil (m := ((2 * k : Nat) : Real)) ha ha1
    (by exact_mod_cast (show 1 ≤ 2 * k by omega)) (2 * k - 1)

/-- **The even zero-core density is triple-exponentially small.** -/
theorem globalEvenColumnZeroDensity_le_triple_exp {alpha : Real} (ha : 0 < alpha)
    (ha1 : alpha ≤ 1) {k : Nat} (hk : 1 ≤ k) :
    globalEvenColumnZeroDensity alpha k ≤
      Real.exp (-(2 : Real) ^ (13 ^ columnSpectrumCap (columnEightDensity alpha)) / 2) := by
  have hM : 1 ≤ globalEvenColumnModelCount alpha k := by
    have hδ0 := globalColumnWordDensity_pos ha ha1 (2 * k - 1)
    exact Nat.ceil_pos.mpr (by positivity)
  have hm : (1 : Real) ≤ 5 * k := by
    have : (1 : Real) ≤ k := by exact_mod_cast hk
    linarith
  have h := elimination_density_le (g := globalEvenColumnModelRank alpha k)
    (d := columnSpectrumCap (columnEightDensity alpha))
    (globalColumnModelRadius_pos ha ha1 (2 * k - 1))
    (globalColumnModelRadius_le_one ha ha1 (2 * k - 1)) hM hm
    (globalColumnVertexDensity_pos ha ha1).le (globalColumnVertexDensity_le_one ha ha1)
  have hpow : (2 : Real) ^ (13 ^ columnSpectrumCap (columnEightDensity alpha)) ≤
      (2 : Real) ^ globalEvenColumnModelRank alpha k :=
    pow_le_pow_right₀ (by norm_num) (globalEvenColumnModelRank_ge ha ha1 hk)
  unfold globalEvenColumnZeroDensity
  dsimp only
  exact h.trans (Real.exp_le_exp.mpr (by linarith))

theorem triple_exp_le_one (d : Nat) : Real.exp (-(2 : Real) ^ (13 ^ d) / 2) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  have : (0 : Real) < 2 ^ (13 ^ d) := by positivity
  linarith

/-- A power `z^16/c` with `c ≥ 1` of a density `z ∈ (0,1]` stays below `z`. -/
theorem pow_sixteen_div_le {z c : Real} (hz : 0 < z) (hz1 : z ≤ 1) (hc : 1 ≤ c) :
    z ^ 16 / c ≤ z := by
  have h1 : z ^ 16 ≤ z := pow_le_of_le_one hz.le hz1 (by norm_num)
  have h2 : z ^ 16 / c ≤ z ^ 16 := div_le_self (by positivity) hc
  linarith

/-- **The coherent-anchor density is triple-exponentially small.** -/
theorem globalCoherentAnchorDensity_le_triple_exp {alpha : Real} (ha : 0 < alpha)
    (ha1 : alpha ≤ 1) :
    globalCoherentAnchorDensity alpha ≤
      Real.exp (-(2 : Real) ^ (13 ^ columnSpectrumCap (columnEightDensity alpha)) / 2) := by
  have hz := globalEvenColumnZeroDensity_le_triple_exp ha ha1 (k := 4) (by norm_num)
  have hz0 := globalEvenColumnZeroDensity_pos (k := 4) ha ha1
  have hz1 := hz.trans (triple_exp_le_one _)
  unfold globalCoherentAnchorDensity
  exact (pow_sixteen_div_le hz0 hz1 (by norm_num)).trans hz

/-- **The coherent-anchor tolerance is triple-exponentially small.** -/
theorem globalCoherentAnchorTolerance_le_triple_exp {alpha : Real} (ha : 0 < alpha)
    (ha1 : alpha ≤ 1) :
    globalCoherentAnchorTolerance alpha ≤
      Real.exp (-(2 : Real) ^ (13 ^ columnSpectrumCap (columnEightDensity alpha)) / 2) := by
  have hz := globalEvenColumnZeroDensity_le_triple_exp ha ha1 (k := 4) (by norm_num)
  have hz0 := globalEvenColumnZeroDensity_pos (k := 4) ha ha1
  have hz1 := hz.trans (triple_exp_le_one _)
  unfold globalCoherentAnchorTolerance
  exact (pow_sixteen_div_le hz0 hz1 (by norm_num)).trans hz

/-- **The coherent-anchor rank bound is exponential in the spectrum cap.** -/
theorem globalCoherentAnchorRank_ge {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    13 ^ columnSpectrumCap (columnEightDensity alpha) ≤ globalCoherentAnchorRank alpha :=
  (globalEvenColumnModelRank_ge ha ha1 (k := 4) (by norm_num)).trans (Nat.le_add_right _ _)

/-- **The coherent-anchor chain cannot supply a polynomial deep-structure bound.** -/
theorem globalCoherentAnchorDensity_lt_polynomial_contract {alpha : Real}
    (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) {K : Nat} (hK : K ≤ 2 ^ 64) :
    globalCoherentAnchorDensity alpha < Real.exp (-(4 / alpha) ^ K) :=
  lt_polynomial_contract_of_le_triple_exp ha ha2 hK
    (globalCoherentAnchorDensity_le_triple_exp ha (by linarith))

end LeanProofs.GowersSzemeredi
