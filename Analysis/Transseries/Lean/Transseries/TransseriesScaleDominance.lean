import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field

/-!
# Lexicographic dominance of power–logarithmic monomials

The transseries volume's `plt:lem:mot-dominance`, the statement that
makes `{X^a (log X)^b}` an asymptotic scale.  For real exponents, as
`X → +∞`,

`X^a (log X)^b / (X^a' (log X)^b') → 0, 1, +∞`

according as `(a,b)` is lexicographically smaller than, equal to, or
larger than `(a',b')`.  The logarithm is *slower than every positive
power*, so the first coordinate decides and the second only breaks ties.

Consequently the scale is totally ordered by the lexicographic order,
and in the volume's generators `t = X⁻¹`, `L = log X` the dominance
`tⁿLʲ ≻ tᵐLᵏ` reads `n < m`, or `n = m` and `j > k` — recorded here as
`plMonomial_generators_dominance`.

* `plMonomial a b X = X^a (log X)^b` (real `rpow` in both slots).
* `tendsto_plMonomial_atTop_zero` — `X^c (log X)^d → 0` for `c < 0` and
  *any* `d`: the quantitative form of "logarithms lose to powers".
* `tendsto_plMonomial_div_atTop_zero` — the lexicographically smaller
  monomial is dominated.
* `tendsto_plMonomial_div_atTop_one`, `tendsto_plMonomial_div_atTop` —
  the other two cases.
-/

set_option autoImplicit false

open Filter Topology Asymptotics Real

namespace Fabius

/-- The power–logarithmic monomial `X^a (log X)^b`, with real exponents
in both slots. -/
noncomputable def plMonomial (a b X : ℝ) : ℝ :=
  X ^ a * Real.log X ^ b

/-- **Logarithms lose to powers**: for a *negative* power `c` and an
arbitrary logarithmic exponent `d`, `X^c (log X)^d → 0`.  The proof
gives away half of the power to absorb the logarithm:
`(log X)^d = o(X^{-c/2})`, so the product is `o(X^{c/2})`. -/
theorem tendsto_plMonomial_atTop_zero {c : ℝ} (hc : c < 0) (d : ℝ) :
    Tendsto (fun X => plMonomial c d X) atTop (𝓝 0) := by
  have hs : (0 : ℝ) < -c / 2 := by linarith
  have hlog : (fun X : ℝ => Real.log X ^ d) =o[atTop] fun X : ℝ => X ^ (-c / 2) :=
    isLittleO_log_rpow_rpow_atTop d hs
  have hmul : (fun X : ℝ => X ^ c * Real.log X ^ d) =o[atTop]
      fun X : ℝ => X ^ c * X ^ (-c / 2) :=
    (isBigO_refl (fun X : ℝ => X ^ c) atTop).mul_isLittleO hlog
  have hhalf : Tendsto (fun X : ℝ => X ^ c * X ^ (-c / 2)) atTop (𝓝 0) := by
    have hev : (fun X : ℝ => X ^ c * X ^ (-c / 2))
        =ᶠ[atTop] fun X : ℝ => X ^ (-(-c / 2)) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
      rw [← Real.rpow_add hX]
      ring_nf
    exact (tendsto_rpow_neg_atTop hs).congr' hev.symm
  exact hmul.isBigO.trans_tendsto hhalf

/-- The ratio of two monomials is the monomial of the differences, for
`X > 1` (where both `X` and `log X` are positive). -/
theorem plMonomial_div_eventuallyEq (a b a' b' : ℝ) :
    (fun X => plMonomial a b X / plMonomial a' b' X) =ᶠ[atTop]
      fun X => plMonomial (a - a') (b - b') X := by
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  have hX0 : (0 : ℝ) < X := lt_trans zero_lt_one hX
  have hL : (0 : ℝ) < Real.log X := Real.log_pos hX
  rw [plMonomial, plMonomial, plMonomial, Real.rpow_sub hX0, Real.rpow_sub hL]
  field_simp

/-- **Dominance, the null case.**  If `(a,b)` is lexicographically
smaller than `(a',b')` then the first monomial is negligible against the
second. -/
theorem tendsto_plMonomial_div_atTop_zero {a b a' b' : ℝ}
    (h : a < a' ∨ (a = a' ∧ b < b')) :
    Tendsto (fun X => plMonomial a b X / plMonomial a' b' X) atTop (𝓝 0) := by
  refine Tendsto.congr' (plMonomial_div_eventuallyEq a b a' b').symm ?_
  rcases h with hlt | ⟨rfl, hblt⟩
  · exact tendsto_plMonomial_atTop_zero (by linarith) _
  · -- equal powers: the ratio is a negative power of the logarithm
    have hd : b - b' < 0 := by linarith
    have hcomp : Tendsto (fun X : ℝ => Real.log X ^ (-(b' - b))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < b' - b)).comp
        Real.tendsto_log_atTop
    refine hcomp.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    have hX0 : (0 : ℝ) < X := lt_trans zero_lt_one hX
    show Real.log X ^ (-(b' - b)) = plMonomial (a - a) (b - b') X
    rw [plMonomial, sub_self, Real.rpow_zero, one_mul]
    ring_nf

/-- **Dominance, the equal case**: identical exponents give ratio one. -/
theorem tendsto_plMonomial_div_atTop_one (a b : ℝ) :
    Tendsto (fun X => plMonomial a b X / plMonomial a b X) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  have hX0 : (0 : ℝ) < X := lt_trans zero_lt_one hX
  have hL : (0 : ℝ) < Real.log X := Real.log_pos hX
  have hne : plMonomial a b X ≠ 0 := by
    rw [plMonomial]
    positivity
  exact (div_self hne).symm

/-- Monomials are positive beyond `X = 1`. -/
theorem plMonomial_pos {a b X : ℝ} (hX : 1 < X) : 0 < plMonomial a b X := by
  have hL : (0 : ℝ) < Real.log X := Real.log_pos hX
  rw [plMonomial]
  positivity

/-- **Dominance, the divergent case.**  If `(a,b)` is lexicographically
larger than `(a',b')` then the ratio tends to `+∞`. -/
theorem tendsto_plMonomial_div_atTop {a b a' b' : ℝ}
    (h : a' < a ∨ (a' = a ∧ b' < b)) :
    Tendsto (fun X => plMonomial a b X / plMonomial a' b' X) atTop atTop := by
  have hzero : Tendsto (fun X => plMonomial a' b' X / plMonomial a b X) atTop
      (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (tendsto_plMonomial_div_atTop_zero h) ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    exact div_pos (plMonomial_pos hX) (plMonomial_pos hX)
  have hinv := tendsto_inv_nhdsGT_zero.comp hzero
  refine hinv.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  show (plMonomial a' b' X / plMonomial a b X)⁻¹ =
    plMonomial a b X / plMonomial a' b' X
  rw [inv_div]

/-- **The forward generator-dominance rule.**  With `t = X⁻¹` and
`L = log X`, the monomial `tⁿLʲ` is `plMonomial (-n) j`. Thus `n < m`, or
`n = m` and `j > k`, makes `tᵐLᵏ / tⁿLʲ` tend to zero. Together with the
preceding equal- and reverse-order limit theorems, this gives the exhaustive
trichotomy printed as `plt:eq:mot-dominance`. -/
theorem plMonomial_generators_dominance {n m j k : ℤ}
    (h : n < m ∨ (n = m ∧ k < j)) :
    Tendsto (fun X => plMonomial (-(m : ℝ)) (k : ℝ) X /
      plMonomial (-(n : ℝ)) (j : ℝ) X) atTop (𝓝 0) := by
  refine tendsto_plMonomial_div_atTop_zero ?_
  rcases h with hlt | ⟨rfl, hkj⟩
  · exact Or.inl (by exact_mod_cast neg_lt_neg (by exact_mod_cast hlt))
  · exact Or.inr ⟨rfl, by exact_mod_cast hkj⟩

end Fabius
