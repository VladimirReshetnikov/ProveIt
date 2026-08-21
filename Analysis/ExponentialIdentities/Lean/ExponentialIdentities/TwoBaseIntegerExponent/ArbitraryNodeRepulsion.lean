import ExponentialIdentities.TwoBaseIntegerExponent.ArbitraryNodeDeterminant
import ExponentialIdentities.TwoBaseIntegerExponent.HigherDifference
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Order.Interval.Finset.Fin

/-!
# Arbitrary-node lattice repulsion for two-base candidates

`ArbitraryNodeDeterminant` supplies the arithmetic half of the arbitrary-node repulsion
theorem: the interpolation matrix on candidate nodes has integer entries, so a nonzero
determinant has absolute value at least one, and the Vandermonde product is positive on
strictly increasing nodes.  What that file leaves as an unanalysed input is the bridge
`det = V * dd` between the determinant and a *divided difference*, together with an upper
bound on the divided difference.  This module supplies the first of the two, unconditionally,
and then derives the repulsion inequality from an explicitly named mean-value hypothesis.

## The divided difference

Mathlib has no divided differences, so `dividedDiff` is defined here as the closed Newton
form

```
f[x 0, …, x r] = ∑ i, f (x i) / ∏_{j ≠ i} (x i - x j).
```

## The determinant identity (unconditional)

`det_interpolationMatrix_eq_vandermonde_mul_dividedDiff` proves the classical identity

```
det ⎛ 1  x₀  ⋯  x₀ ^ (r-1)  f x₀ ⎞
    ⎜ 1  x₁  ⋯  x₁ ^ (r-1)  f x₁ ⎟ = V (x 0, …, x r) * f[x 0, …, x r]
    ⎝ ⋮  ⋮        ⋮          ⋮   ⎠
```

for arbitrary pairwise distinct real nodes and an arbitrary function `f`.  The proof avoids
cofactor expansion entirely.  Interpolating `f` at the nodes by a polynomial `P` of degree at
most `r`:

* the final column of the matrix becomes the column of values of `P`, hence a linear
  combination `∑ d, P.coeff d • (ordinary power column d)` of the columns of the Vandermonde
  matrix; `Matrix.det_updateCol_sum` then evaluates the determinant as
  `P.coeff r * det (vandermonde x)`, and `Matrix.det_vandermonde` identifies the latter with
  the Vandermonde product;
* `Lagrange.coeff_eq_sum` identifies `P.coeff r` with the Newton sum, i.e. with
  `dividedDiff r x f`.

The two halves are proved separately as `det_interpolationMatrix_eq_of_polynomial` and
`exists_interpolant_dividedDiff_eq_coeff`, and combined in the main identity.

## The mean-value input (a hypothesis, not a theorem)

The remaining analytic ingredient of the report's arbitrary-node theorem is the generalized
mean-value theorem for divided differences, `f[x 0, …, x r] = f⁽ʳ⁾ ξ / r !` for some interior
`ξ`.  Mathlib has no divided differences and hence no such theorem, and the repository's
`HigherDifference` proves the corresponding statement only for *equally spaced* nodes.  It is
therefore packaged here as an explicit predicate `RpowDividedDifferenceMeanValue`, carried as
a hypothesis by the repulsion theorem.  Everything else in this file is unconditional.

## Main results

Unconditional:

* `dividedDiff`, `realVandermondeProduct` and their basic lemmas;
* `exists_interpolant_dividedDiff_eq_coeff`;
* `det_interpolationMatrix_eq_of_polynomial`;
* `det_interpolationMatrix_eq_vandermonde_mul_dividedDiff` (the determinant identity);
* `dividedDiff_eq_coeff_of_polynomial` and `dividedDiff_pow`;
* `det_nodeMatrix_eq_vandermondeProduct_mul_dividedDiff`;
* `vandermondeProduct_le_pow` and `two_mul_pairCount`.

Conditional on `RpowDividedDifferenceMeanValue`:

* `le_vandermondeProduct_of_dividedDiffMeanValue`, the repulsion inequality
  `r ! / |(θ)_r| * m 0 ^ (r - θ) ≤ ∏_{i < j} (m j - m i)`;
* `packing_of_dividedDiffMeanValue`, its local-packing form.
-/

open Set
open scoped Nat

namespace LeanProofs.TwoBaseIntegerExponent

noncomputable section

/-! ## Divided differences -/

/-- The Newton divided difference `f[x 0, …, x r]` of `f` at the nodes `x 0, …, x r`, in the
closed form `∑ i, f (x i) / ∏_{j ≠ i} (x i - x j)`.

Mathlib has no divided differences, so this is the working definition throughout the module.
For pairwise distinct nodes it agrees with the coefficient of `t ^ r` in the interpolating
polynomial; see `dividedDiff_eq_coeff_of_polynomial`. -/
def dividedDiff (r : ℕ) (x : Fin (r + 1) → ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ i : Fin (r + 1), f (x i) / ∏ j ∈ Finset.univ.erase i, (x i - x j)

/-- Defining equation of `dividedDiff`. -/
theorem dividedDiff_def (r : ℕ) (x : Fin (r + 1) → ℝ) (f : ℝ → ℝ) :
    dividedDiff r x f =
      ∑ i : Fin (r + 1), f (x i) / ∏ j ∈ Finset.univ.erase i, (x i - x j) := rfl

/-! ## The Vandermonde product of arbitrary real nodes -/

/-- The Vandermonde product `∏_{i < j} (x j - x i)` of arbitrary real nodes.  For natural
nodes this is `vandermondeProduct` of `ArbitraryNodeDeterminant`. -/
def realVandermondeProduct (r : ℕ) (x : Fin (r + 1) → ℝ) : ℝ :=
  ∏ i : Fin (r + 1), ∏ j ∈ Finset.Ioi i, (x j - x i)

/-- The real-node Vandermonde product is the determinant of the Vandermonde matrix. -/
theorem realVandermondeProduct_eq_det (r : ℕ) (x : Fin (r + 1) → ℝ) :
    realVandermondeProduct r x = (Matrix.vandermonde x).det :=
  (Matrix.det_vandermonde x).symm

/-- On natural nodes the real-node Vandermonde product is the one used by
`ArbitraryNodeDeterminant`. -/
theorem realVandermondeProduct_natCast (r : ℕ) (m : Fin (r + 1) → ℕ) :
    realVandermondeProduct r (fun i ↦ (m i : ℝ)) = vandermondeProduct r m := rfl

/-- **Pairwise distinct nodes have nonzero Vandermonde product.** -/
theorem realVandermondeProduct_ne_zero (r : ℕ) (x : Fin (r + 1) → ℝ)
    (hx : Function.Injective x) : realVandermondeProduct r x ≠ 0 := by
  rw [realVandermondeProduct_eq_det]
  intro h
  obtain ⟨i, j, hij, hne⟩ := Matrix.det_vandermonde_eq_zero_iff.mp h
  exact hne (hx hij)

/-! ## The divided difference as an interpolation coefficient -/

/-- **The divided difference is the top coefficient of the interpolating polynomial.**  For
pairwise distinct nodes there is a polynomial `P` of degree at most `r` matching `f` at every
node, and `dividedDiff r x f` is its coefficient of `t ^ r`.

The interpolant is Mathlib's `Lagrange.interpolate`, and the coefficient identification is
`Lagrange.coeff_eq_sum`. -/
theorem exists_interpolant_dividedDiff_eq_coeff (r : ℕ) (x : Fin (r + 1) → ℝ)
    (hx : Function.Injective x) (f : ℝ → ℝ) :
    ∃ P : Polynomial ℝ, P.natDegree ≤ r ∧ (∀ i, P.eval (x i) = f (x i)) ∧
      dividedDiff r x f = P.coeff r := by
  have hvs : Set.InjOn x ↑(Finset.univ : Finset (Fin (r + 1))) := hx.injOn
  have hcard : (Finset.univ : Finset (Fin (r + 1))).card = r + 1 := by simp
  refine ⟨Lagrange.interpolate Finset.univ x (fun i ↦ f (x i)), ?_, ?_, ?_⟩
  · have h := Lagrange.degree_interpolate_le (fun i ↦ f (x i)) hvs
    rw [hcard, Nat.add_sub_cancel] at h
    exact Polynomial.natDegree_le_iff_degree_le.mpr h
  · intro i
    exact Lagrange.eval_interpolate_at_node _ hvs (Finset.mem_univ i)
  · have hdeglt := Lagrange.degree_interpolate_lt (fun i ↦ f (x i)) hvs
    have h := Lagrange.coeff_eq_sum hvs hdeglt
    rw [hcard, Nat.add_sub_cancel] at h
    rw [dividedDiff_def, h]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Lagrange.eval_interpolate_at_node _ hvs (Finset.mem_univ i)]

/-! ## The determinant identity -/

/-- **Determinant of the interpolation matrix through a matching polynomial.**  If `P` has
degree at most `r` and agrees with `f` at all the nodes, then the interpolation determinant is
the Vandermonde product times the coefficient of `t ^ r` in `P`.

The last column of the matrix is then a linear combination of the ordinary-power columns with
coefficients the coefficients of `P`, and `Matrix.det_updateCol_sum` evaluates the
determinant.  No hypothesis on the nodes is needed here. -/
theorem det_interpolationMatrix_eq_of_polynomial (r : ℕ) (x : Fin (r + 1) → ℝ) (f : ℝ → ℝ)
    (P : Polynomial ℝ) (hdeg : P.natDegree ≤ r) (hnode : ∀ i, P.eval (x i) = f (x i)) :
    (interpolationMatrix r x f).det = realVandermondeProduct r x * P.coeff r := by
  have hnatdeg : P.natDegree < r + 1 := by omega
  have hval : ∀ i : Fin (r + 1),
      (∑ d : Fin (r + 1), P.coeff (d : ℕ) • Matrix.vandermonde x i d) = f (x i) := by
    intro i
    have h1 : P.eval (x i) = ∑ d ∈ Finset.range (r + 1), P.coeff d * x i ^ d :=
      Polynomial.eval_eq_sum_range' hnatdeg (x i)
    have h2 : (∑ d ∈ Finset.range (r + 1), P.coeff d * x i ^ d)
        = ∑ d : Fin (r + 1), P.coeff (d : ℕ) * x i ^ (d : ℕ) :=
      (Fin.sum_univ_eq_sum_range (fun d ↦ P.coeff d * x i ^ d) (r + 1)).symm
    have h3 : (∑ d : Fin (r + 1), P.coeff (d : ℕ) • Matrix.vandermonde x i d)
        = ∑ d : Fin (r + 1), P.coeff (d : ℕ) * x i ^ (d : ℕ) :=
      Finset.sum_congr rfl fun d _ ↦ by rw [Matrix.vandermonde_apply, smul_eq_mul]
    rw [h3, ← h2, ← h1, hnode i]
  have hmat : interpolationMatrix r x f
      = (Matrix.vandermonde x).updateCol (Fin.last r)
          (fun k ↦ ∑ d : Fin (r + 1), P.coeff (d : ℕ) • Matrix.vandermonde x k d) := by
    ext i j
    by_cases hj : j = Fin.last r
    · subst hj
      rw [interpolationMatrix_apply_last, Matrix.updateCol_self]
      exact (hval i).symm
    · rw [interpolationMatrix_apply_of_ne r x f hj, Matrix.updateCol_ne hj]
      exact (Matrix.vandermonde_apply x i j).symm
  rw [hmat, Matrix.det_updateCol_sum]
  simp only [Fin.val_last, smul_eq_mul]
  rw [realVandermondeProduct_eq_det]
  ring

/-- **The arbitrary-node determinant/divided-difference identity.**  For pairwise distinct
real nodes and an arbitrary function `f`,

```
det (interpolationMatrix r x f) = V (x 0, …, x r) * f[x 0, …, x r].
```

This is equation `df:det-divdiff` of the report, proved unconditionally.  It is the algebraic
half of the arbitrary-node repulsion theorem; the analytic half is the divided-difference mean
value theorem, which is taken as a hypothesis below. -/
theorem det_interpolationMatrix_eq_vandermonde_mul_dividedDiff (r : ℕ) (x : Fin (r + 1) → ℝ)
    (hx : Function.Injective x) (f : ℝ → ℝ) :
    (interpolationMatrix r x f).det = realVandermondeProduct r x * dividedDiff r x f := by
  obtain ⟨P, hdeg, hnode, hcoeff⟩ := exists_interpolant_dividedDiff_eq_coeff r x hx f
  rw [hcoeff]
  exact det_interpolationMatrix_eq_of_polynomial r x f P hdeg hnode

/-- **Uniqueness form of the interpolation coefficient.**  For pairwise distinct nodes, the
divided difference of *any* polynomial of degree at most `r` is its coefficient of `t ^ r`. -/
theorem dividedDiff_eq_coeff_of_polynomial (r : ℕ) (x : Fin (r + 1) → ℝ)
    (hx : Function.Injective x) (P : Polynomial ℝ) (hdeg : P.natDegree ≤ r) :
    dividedDiff r x (fun t ↦ P.eval t) = P.coeff r := by
  have h1 :=
    det_interpolationMatrix_eq_vandermonde_mul_dividedDiff r x hx (fun t ↦ P.eval t)
  have h2 := det_interpolationMatrix_eq_of_polynomial r x (fun t ↦ P.eval t) P hdeg
    (fun _ ↦ rfl)
  have h3 : realVandermondeProduct r x * dividedDiff r x (fun t ↦ P.eval t)
      = realVandermondeProduct r x * P.coeff r := by rw [← h1, h2]
  exact mul_left_cancel₀ (realVandermondeProduct_ne_zero r x hx) h3

/-- **Divided differences of the monomials.**  For pairwise distinct nodes and `k ≤ r`, the
`r`-th divided difference of `t ↦ t ^ k` is `1` when `k = r` and `0` otherwise.  This is the
Kronecker normalization that makes the determinant identity a genuine factorization. -/
theorem dividedDiff_pow (r : ℕ) (x : Fin (r + 1) → ℝ) (hx : Function.Injective x) {k : ℕ}
    (hk : k ≤ r) : dividedDiff r x (fun t ↦ t ^ k) = if r = k then 1 else 0 := by
  have hdeg : ((Polynomial.X : Polynomial ℝ) ^ k).natDegree ≤ r := by
    rw [Polynomial.natDegree_X_pow]
    exact hk
  have h := dividedDiff_eq_coeff_of_polynomial r x hx ((Polynomial.X : Polynomial ℝ) ^ k) hdeg
  have hfun : (fun t : ℝ ↦ Polynomial.eval t ((Polynomial.X : Polynomial ℝ) ^ k))
      = fun t : ℝ ↦ t ^ k := by
    funext t
    simp
  rw [hfun] at h
  rw [h, Polynomial.coeff_X_pow]

/-! ## Specialization to candidate nodes -/

/-- **The node determinant factors through the divided difference.**  For strictly increasing
natural nodes, the arbitrary-node matrix of `ArbitraryNodeDeterminant` has determinant equal
to the Vandermonde product times the `r`-th divided difference of `t ↦ t ^ θ`.

This is exactly the input that `abs_det_nodeMatrix_le_of_dividedDifference` and its corollaries
were phrased to consume. -/
theorem det_nodeMatrix_eq_vandermondeProduct_mul_dividedDiff (r : ℕ) (m : Fin (r + 1) → ℕ)
    (hstrict : StrictMono m) :
    (nodeMatrix r m).det = vandermondeProduct r m *
      dividedDiff r (fun i ↦ (m i : ℝ)) (fun t ↦ t ^ logThreeDivLogTwo) := by
  have hx : Function.Injective (fun i ↦ ((m i : ℝ))) := by
    intro i j hij
    have hcast : (m i : ℝ) = (m j : ℝ) := hij
    exact hstrict.injective (by exact_mod_cast hcast)
  show (interpolationMatrix r (fun i ↦ (m i : ℝ)) (fun t ↦ t ^ logThreeDivLogTwo)).det
      = realVandermondeProduct r (fun i ↦ (m i : ℝ)) *
        dividedDiff r (fun i ↦ (m i : ℝ)) (fun t ↦ t ^ logThreeDivLogTwo)
  exact det_interpolationMatrix_eq_vandermonde_mul_dividedDiff r (fun i ↦ (m i : ℝ)) hx _

/-! ## The mean-value hypothesis -/

/-- **The divided-difference mean value property for a real power.**  This is the analytic
input `df:divdiff-mvt` of the report: some interior point `ξ` realizes

```
f[x 0, …, x r] = f⁽ʳ⁾ ξ / r !,     f t = t ^ α,     f⁽ʳ⁾ t = (α)_r * t ^ (α - r).
```

Mathlib has no divided differences and hence no mean value theorem for them, and the
repository's `HigherDifference` proves the corresponding statement only for equally spaced
nodes.  The property is therefore stated here as a predicate and carried as a hypothesis; it
is *not* proved in this file. -/
def RpowDividedDifferenceMeanValue (α : ℝ) (r : ℕ) (x : Fin (r + 1) → ℝ) : Prop :=
  ∃ ξ : ℝ, x 0 < ξ ∧ ξ < x (Fin.last r) ∧
    dividedDiff r x (fun t ↦ t ^ α) = fallingRpowCoeff α r * ξ ^ (α - (r : ℝ)) / (r ! : ℝ)

/-! ## The arbitrary-node repulsion theorem -/

/-- **Arbitrary-node lattice repulsion, conditional on the mean value input.**  Let
`1 ≤ m 0 < m 1 < ⋯ < m r` be natural two-base candidates and suppose the divided-difference
mean value property holds for `t ↦ t ^ θ` at these nodes.  Then

```
r ! / |(θ)_r| * m 0 ^ (r - θ) ≤ ∏_{i < j} (m j - m i).
```

This is Theorem `df:thm-arbitrary-node` of the report.  Everything except the hypothesis
`hmv` is unconditional: the integrality and `1 ≤ |det|` come from `ArbitraryNodeDeterminant`,
the factorization `det = V * dd` from
`det_nodeMatrix_eq_vandermondeProduct_mul_dividedDiff` above, and the bound `ξ ^ (θ - r) ≤
m 0 ^ (θ - r)` from the negativity of the exponent. -/
theorem le_vandermondeProduct_of_dividedDiffMeanValue {r : ℕ} (hr : 2 ≤ r)
    (m : Fin (r + 1) → ℕ) (hstrict : StrictMono m)
    (hcand : ∀ i, TwoBaseNaturalCandidate (m i))
    (hmv : RpowDividedDifferenceMeanValue logThreeDivLogTwo r (fun i ↦ (m i : ℝ))) :
    (r ! : ℝ) / |fallingRpowCoeff logThreeDivLogTwo r| *
        (m 0 : ℝ) ^ ((r : ℝ) - logThreeDivLogTwo) ≤ vandermondeProduct r m := by
  obtain ⟨xi, hxi0, -, hddval⟩ := hmv
  have hxi0' : (m 0 : ℝ) < xi := hxi0
  have hcne : fallingRpowCoeff logThreeDivLogTwo r ≠ 0 :=
    fallingRpowCoeff_logThreeDivLogTwo_ne_zero r
  have hcpos : 0 < |fallingRpowCoeff logThreeDivLogTwo r| := abs_pos.mpr hcne
  have hFpos : (0 : ℝ) < (r ! : ℝ) := by exact_mod_cast r.factorial_pos
  have hm0R : (0 : ℝ) < (m 0 : ℝ) := by exact_mod_cast (hcand 0).1
  have hxipos : (0 : ℝ) < xi := hm0R.trans hxi0'
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hexp : logThreeDivLogTwo - (r : ℝ) < 0 := by
    linarith [logThreeDivLogTwo_lt_eight_fifths]
  have hApos : (0 : ℝ) < (m 0 : ℝ) ^ ((r : ℝ) - logThreeDivLogTwo) :=
    Real.rpow_pos_of_pos hm0R _
  have hAA : (m 0 : ℝ) ^ ((r : ℝ) - logThreeDivLogTwo) *
      (m 0 : ℝ) ^ (logThreeDivLogTwo - (r : ℝ)) = 1 := by
    rw [← Real.rpow_add hm0R]
    norm_num
  have hVpos : 0 < vandermondeProduct r m := vandermondeProduct_pos r m hstrict
  have hdet := det_nodeMatrix_eq_vandermondeProduct_mul_dividedDiff r m hstrict
  have hddne :
      dividedDiff r (fun i ↦ (m i : ℝ)) (fun t ↦ t ^ logThreeDivLogTwo) ≠ 0 := by
    rw [hddval]
    exact div_ne_zero (mul_ne_zero hcne (Real.rpow_pos_of_pos hxipos _).ne') hFpos.ne'
  have hne : (nodeMatrix r m).det ≠ 0 := by
    rw [hdet]
    exact mul_ne_zero hVpos.ne' hddne
  have habs : |dividedDiff r (fun i ↦ (m i : ℝ)) (fun t ↦ t ^ logThreeDivLogTwo)| =
      |fallingRpowCoeff logThreeDivLogTwo r| * xi ^ (logThreeDivLogTwo - (r : ℝ)) /
        (r ! : ℝ) := by
    rw [hddval, abs_div, abs_mul,
      abs_of_pos (Real.rpow_pos_of_pos hxipos (logThreeDivLogTwo - (r : ℝ))),
      abs_of_pos hFpos]
  have hpow : xi ^ (logThreeDivLogTwo - (r : ℝ)) ≤
      (m 0 : ℝ) ^ (logThreeDivLogTwo - (r : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hm0R hxi0'.le hexp.le
  have hbound : |dividedDiff r (fun i ↦ (m i : ℝ)) (fun t ↦ t ^ logThreeDivLogTwo)| ≤
      |fallingRpowCoeff logThreeDivLogTwo r| *
        (m 0 : ℝ) ^ (logThreeDivLogTwo - (r : ℝ)) / (r ! : ℝ) := by
    rw [habs, div_le_div_iff₀ hFpos hFpos]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (abs_nonneg _)) hFpos.le
  have hkey := one_le_vandermondeProduct_mul_of_dividedDifference r m hstrict hcand hdet
    hbound hne
  have hkey' : (1 : ℝ) ≤ vandermondeProduct r m *
      (|fallingRpowCoeff logThreeDivLogTwo r| *
        (m 0 : ℝ) ^ (logThreeDivLogTwo - (r : ℝ))) / (r ! : ℝ) := by
    rw [mul_div_assoc]
    exact hkey
  rw [le_div_iff₀ hFpos] at hkey'
  rw [div_mul_eq_mul_div, div_le_iff₀ hcpos]
  have h2 : (r ! : ℝ) ≤ vandermondeProduct r m *
      (|fallingRpowCoeff logThreeDivLogTwo r| *
        (m 0 : ℝ) ^ (logThreeDivLogTwo - (r : ℝ))) := by linarith
  have h3 : (r ! : ℝ) * (m 0 : ℝ) ^ ((r : ℝ) - logThreeDivLogTwo) ≤
      vandermondeProduct r m *
        (|fallingRpowCoeff logThreeDivLogTwo r| *
          (m 0 : ℝ) ^ (logThreeDivLogTwo - (r : ℝ))) *
        (m 0 : ℝ) ^ ((r : ℝ) - logThreeDivLogTwo) :=
    mul_le_mul_of_nonneg_right h2 hApos.le
  have h4 : vandermondeProduct r m *
      (|fallingRpowCoeff logThreeDivLogTwo r| *
        (m 0 : ℝ) ^ (logThreeDivLogTwo - (r : ℝ))) *
      (m 0 : ℝ) ^ ((r : ℝ) - logThreeDivLogTwo) =
        vandermondeProduct r m * |fallingRpowCoeff logThreeDivLogTwo r| := by
    have hrearr : vandermondeProduct r m *
        (|fallingRpowCoeff logThreeDivLogTwo r| *
          (m 0 : ℝ) ^ (logThreeDivLogTwo - (r : ℝ))) *
        (m 0 : ℝ) ^ ((r : ℝ) - logThreeDivLogTwo) =
          vandermondeProduct r m * |fallingRpowCoeff logThreeDivLogTwo r| *
            ((m 0 : ℝ) ^ ((r : ℝ) - logThreeDivLogTwo) *
              (m 0 : ℝ) ^ (logThreeDivLogTwo - (r : ℝ))) := by ring
    rw [hrearr, hAA, mul_one]
  linarith

/-! ## Local packing -/

/-- The number `R_r = r (r + 1) / 2` of ordered pairs among `r + 1` nodes, written as the sum
of the sizes of the strict upper sets. -/
def pairCount (r : ℕ) : ℕ := ∑ i : Fin (r + 1), (Finset.Ioi i).card

/-- `pairCount r` is the binomial coefficient `R_r = r (r + 1) / 2`, stated without natural
division. -/
theorem two_mul_pairCount (r : ℕ) : 2 * pairCount r = r * (r + 1) := by
  have e1 : (∑ i : Fin (r + 1), (Finset.Ioi i).card)
      = ∑ i : Fin (r + 1), (r - (i : ℕ)) :=
    Finset.sum_congr rfl fun i _ ↦ by simp
  have e2 : (∑ i ∈ Finset.range (r + 1), (r - i))
      = ∑ i : Fin (r + 1), (r - (i : ℕ)) :=
    (Fin.sum_univ_eq_sum_range (fun i ↦ r - i) (r + 1)).symm
  have h1 : pairCount r = ∑ i ∈ Finset.range (r + 1), (r - i) := by
    show (∑ i : Fin (r + 1), (Finset.Ioi i).card) = _
    rw [e1, e2]
  have e3 : (∑ i ∈ Finset.range (r + 1), (r - i)) = ∑ i ∈ Finset.range (r + 1), i :=
    Finset.sum_flip (fun k ↦ k)
  have e4 : (∑ i ∈ Finset.range (r + 1), i) * 2 = (r + 1) * r := by
    have h := Finset.sum_range_id_mul_two (r + 1)
    rwa [Nat.add_sub_cancel] at h
  calc 2 * pairCount r = (∑ i ∈ Finset.range (r + 1), i) * 2 := by
        rw [h1, e3]; ring
    _ = (r + 1) * r := e4
    _ = r * (r + 1) := Nat.mul_comm _ _

/-- **The Vandermonde product of nodes in an interval of length `H` is at most
`H ^ R_r`.**  Every pairwise gap of points of `[N, N + H]` is at most `H`, and there are
`pairCount r` of them. -/
theorem vandermondeProduct_le_pow (r : ℕ) (m : Fin (r + 1) → ℕ) (hstrict : StrictMono m)
    {N H : ℝ} (hlo : ∀ i, N ≤ (m i : ℝ)) (hhi : ∀ i, (m i : ℝ) ≤ N + H) :
    vandermondeProduct r m ≤ H ^ pairCount r := by
  have hmono : ∀ i j : Fin (r + 1), j ∈ Finset.Ioi i → (m i : ℝ) ≤ (m j : ℝ) := by
    intro i j hj
    exact_mod_cast hstrict.monotone (le_of_lt (Finset.mem_Ioi.mp hj))
  have hstep : ∀ i : Fin (r + 1),
      (∏ j ∈ Finset.Ioi i, ((m j : ℝ) - (m i : ℝ))) ≤ H ^ (Finset.Ioi i).card := by
    intro i
    calc (∏ j ∈ Finset.Ioi i, ((m j : ℝ) - (m i : ℝ)))
        ≤ ∏ _j ∈ Finset.Ioi i, H := by
          refine Finset.prod_le_prod (fun j hj ↦ ?_) (fun j _ ↦ ?_)
          · linarith [hmono i j hj]
          · linarith [hlo i, hhi j]
      _ = H ^ (Finset.Ioi i).card := Finset.prod_const H
  show (∏ i : Fin (r + 1), ∏ j ∈ Finset.Ioi i, ((m j : ℝ) - (m i : ℝ))) ≤ H ^ pairCount r
  calc (∏ i : Fin (r + 1), ∏ j ∈ Finset.Ioi i, ((m j : ℝ) - (m i : ℝ)))
      ≤ ∏ i : Fin (r + 1), H ^ (Finset.Ioi i).card := by
        refine Finset.prod_le_prod (fun i _ ↦ ?_) (fun i _ ↦ hstep i)
        exact Finset.prod_nonneg fun j hj ↦ by linarith [hmono i j hj]
    _ = H ^ pairCount r := Finset.prod_pow_eq_pow_sum _ _ _

/-- **Local packing of candidates, conditional on the mean value input.**  If `r + 1` natural
two-base candidates lie in `[N, N + H]` with `N ≥ 1` and the divided-difference mean value
property holds at those nodes, then

```
r ! / |(θ)_r| * N ^ (r - θ) ≤ H ^ R_r.
```

This is Corollary `df:cor-r-packing` of the report; contrapositively, an interval that is too
short to satisfy the inequality carries at most `r` candidates. -/
theorem packing_of_dividedDiffMeanValue {r : ℕ} (hr : 2 ≤ r) (m : Fin (r + 1) → ℕ)
    (hstrict : StrictMono m) (hcand : ∀ i, TwoBaseNaturalCandidate (m i))
    (hmv : RpowDividedDifferenceMeanValue logThreeDivLogTwo r (fun i ↦ (m i : ℝ)))
    {N H : ℝ} (hN : 1 ≤ N) (hlo : ∀ i, N ≤ (m i : ℝ)) (hhi : ∀ i, (m i : ℝ) ≤ N + H) :
    (r ! : ℝ) / |fallingRpowCoeff logThreeDivLogTwo r| *
        N ^ ((r : ℝ) - logThreeDivLogTwo) ≤ H ^ pairCount r := by
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hexp : (0 : ℝ) ≤ (r : ℝ) - logThreeDivLogTwo := by
    linarith [logThreeDivLogTwo_lt_eight_fifths]
  have hcoef : (0 : ℝ) ≤ (r ! : ℝ) / |fallingRpowCoeff logThreeDivLogTwo r| := by
    have hFpos : (0 : ℝ) < (r ! : ℝ) := by exact_mod_cast r.factorial_pos
    have hcpos : 0 < |fallingRpowCoeff logThreeDivLogTwo r| :=
      abs_pos.mpr (fallingRpowCoeff_logThreeDivLogTwo_ne_zero r)
    exact le_of_lt (div_pos hFpos hcpos)
  have h3 : N ^ ((r : ℝ) - logThreeDivLogTwo) ≤
      (m 0 : ℝ) ^ ((r : ℝ) - logThreeDivLogTwo) :=
    Real.rpow_le_rpow hNpos.le (hlo 0) hexp
  calc (r ! : ℝ) / |fallingRpowCoeff logThreeDivLogTwo r| *
        N ^ ((r : ℝ) - logThreeDivLogTwo)
      ≤ (r ! : ℝ) / |fallingRpowCoeff logThreeDivLogTwo r| *
          (m 0 : ℝ) ^ ((r : ℝ) - logThreeDivLogTwo) :=
        mul_le_mul_of_nonneg_left h3 hcoef
    _ ≤ vandermondeProduct r m :=
        le_vandermondeProduct_of_dividedDiffMeanValue hr m hstrict hcand hmv
    _ ≤ H ^ pairCount r := vandermondeProduct_le_pow r m hstrict hlo hhi

end

end LeanProofs.TwoBaseIntegerExponent
