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
* `globalColumnZeroRadius_le_inv_two_pow`, `globalEvenColumnZeroRadius_le_inv_two_pow`:
  both zero-core radii are at most `2^(-g)`. Hence any `B` with `exp(-B)` at
  most the radius is at least `13^d/2` (`globalColumnZeroRadius_bound_ge`,
  `globalCoherentAnchorRadius_bound_ge`): the contract's radius condition
  `exp(-Bnd c) ≤ ρ` already needs `Bnd` exponential in `d`.

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

/-! ### The zero-core radius is doubly exponentially small -/

/-- A refinement kernel radius with at least two cells per frequency is at
most `2^(-g)`. -/
theorem refinementKernelRadius_le_inv_two_pow (g e : Nat) {rho r : Real}
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (hr : 0 < r) (hr2 : r ≤ 1 / 2) :
    refinementKernelRadius g e rho r ≤ 1 / 2 ^ g := by
  have hP : (1 : Real) ≤ denseLevelCells rho := by
    exact_mod_cast (Nat.ceil_pos.mpr (by positivity) : 0 < denseLevelCells rho)
  have hQ : (2 : Real) ≤ refinementCells r := by
    have h : (2 : Real) ≤ 1 / r := by rw [le_div_iff₀ hr]; linarith
    exact h.trans (Nat.le_ceil _)
  have hcap : (2 : Real) ^ g ≤ (refinementKernelCap g e rho r : Real) := by
    unfold refinementKernelCap
    push_cast
    calc (2 : Real) ^ g = 1 * 2 ^ g := (one_mul _).symm
      _ ≤ (denseLevelCells rho : Real) ^ g * (refinementCells r : Real) ^ (g + e) :=
        mul_le_mul (one_le_pow₀ hP)
          ((pow_le_pow_left₀ (by norm_num) hQ g).trans
            (pow_le_pow_right₀ (by linarith) (Nat.le_add_right g e)))
          (by positivity) (by positivity)
  have hG : (0 : Real) < 2 ^ g := by positivity
  unfold refinementKernelRadius
  rw [div_le_div_iff₀ (by linarith) hG]
  have := mul_le_mul_of_nonneg_right (show rho / 2 ≤ 1 by linarith) hG.le
  linarith

theorem globalColumnIdentityRadius_le_one {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    globalColumnIdentityRadius alpha ≤ 1 := by
  have hpi : (1 : Real) ≤ 4 * Real.pi := by linarith [Real.pi_gt_three]
  exact (globalColumnIdentityRadius_le ha ha1).trans ((div_le_one (by positivity)).mpr hpi)

/-- **The zero-core radius is at most `2^(-g)`.** -/
theorem globalColumnZeroRadius_le_inv_two_pow {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    globalColumnZeroRadius alpha ≤ 1 / 2 ^ globalColumnModelRank alpha :=
  (min_le_right _ _).trans (refinementKernelRadius_le_inv_two_pow _ _
    (globalColumnIdentityRadius_pos ha ha1) (globalColumnIdentityRadius_le_one ha ha1)
    (by linarith [globalColumnModelRadius_pos ha ha1 3])
    (by linarith [globalColumnModelRadius_le_one ha ha1 3]))

/-- **The even zero-core radius is at most `2^(-g)`.** -/
theorem globalEvenColumnZeroRadius_le_inv_two_pow {alpha : Real} (ha : 0 < alpha)
    (ha1 : alpha ≤ 1) (k : Nat) :
    globalEvenColumnZeroRadius alpha k ≤ 1 / 2 ^ globalEvenColumnModelRank alpha k :=
  (min_le_right _ _).trans (refinementKernelRadius_le_inv_two_pow _ _
    (globalColumnIdentityRadius_pos ha ha1) (globalColumnIdentityRadius_le_one ha ha1)
    (by linarith [globalColumnModelRadius_pos ha ha1 (2 * k - 1)])
    (by linarith [globalColumnModelRadius_le_one ha ha1 (2 * k - 1)]))

/-- A radius at most `2^(-g)` certifies `exp(-B) ≤ ρ` only if `B ≥ g/2`. -/
theorem half_le_of_exp_neg_le_inv_two_pow {B rho : Real} {g : Nat}
    (hrho : rho ≤ 1 / 2 ^ g) (h : Real.exp (-B) ≤ rho) : (g : Real) / 2 ≤ B := by
  have he : (1 : Real) / 2 ^ g = Real.exp (-((g : Real) * Real.log 2)) := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log two_pos, one_div]
  have h2 := Real.exp_le_exp.mp ((h.trans hrho).trans he.le)
  have hlog : (1 / 2 : Real) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hg : (0 : Real) ≤ g := Nat.cast_nonneg g
  nlinarith

/-- **The coherent-anchor radius forces an exponential bound.** Any `B` with
`exp(-B)` at most the radius of `global_coherent_column_anchors` is at least
`13^d/2`, so the contract's `exp(-Bnd c) ≤ ρ` needs `Bnd` exponential in
`d = columnSpectrumCap (columnEightDensity alpha)`. -/
theorem globalCoherentAnchorRadius_bound_ge {alpha B : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (h : Real.exp (-B) ≤ globalEvenColumnZeroRadius alpha 4) :
    ((13 ^ columnSpectrumCap (columnEightDensity alpha) : Nat) : Real) / 2 ≤ B := by
  have hg := half_le_of_exp_neg_le_inv_two_pow
    (globalEvenColumnZeroRadius_le_inv_two_pow ha ha1 4) h
  have hle : ((13 ^ columnSpectrumCap (columnEightDensity alpha) : Nat) : Real) ≤
      globalEvenColumnModelRank alpha 4 := by
    exact_mod_cast globalEvenColumnModelRank_ge ha ha1 (k := 4) (by norm_num)
  linarith

/-- The same for the radius of `global_column_shifted_agreement`. -/
theorem globalColumnZeroRadius_bound_ge {alpha B : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (h : Real.exp (-B) ≤ globalColumnZeroRadius alpha) :
    ((13 ^ columnSpectrumCap (columnEightDensity alpha) : Nat) : Real) / 2 ≤ B := by
  have hg := half_le_of_exp_neg_le_inv_two_pow (globalColumnZeroRadius_le_inv_two_pow ha ha1) h
  have hle : ((13 ^ columnSpectrumCap (columnEightDensity alpha) : Nat) : Real) ≤
      globalColumnModelRank alpha := by
    exact_mod_cast thirteen_pow_le_globalColumnModelRank ha ha1
  linarith

end LeanProofs.GowersSzemeredi
