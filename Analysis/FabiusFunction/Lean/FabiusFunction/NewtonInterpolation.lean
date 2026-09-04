import FabiusFunction.FiniteQBinomialCore
import Mathlib.LinearAlgebra.Lagrange

/-!
# Newton interpolation, and the geometric grid `1, q, q², …`

For nodes `v 0, v 1, …` in a field and data `y 0, y 1, …`, the **Newton coefficients**
are defined by triangular elimination,

`c_k = (y_k - ∑_{r<k} c_r ∏_{j<r} (v_k - v_j)) / ∏_{j<k} (v_k - v_j)`,

so that the **Newton polynomial** `P_n = ∑_{k≤n} c_k ∏_{j<k} (X - v_j)` interpolates the
data at `v_0, …, v_n` by construction: at `v_i` every basis polynomial with `k > i`
vanishes and the `k = i` term contributes exactly what is missing.  When the nodes are
distinct, `P_n` is Mathlib's Lagrange interpolant, and reading off its top coefficient
with `Lagrange.coeff_eq_sum` gives the **divided-difference formula**

`c_k = ∑_{j≤k} y_j / ∏_{r≤k, r≠j} (v_j - v_r)`.

On the geometric grid `v_j = q^j` the Newton basis is
`∏_{r<k} (X - q^r) = (-1)^k q^{C(k,2)} (X; q⁻¹)_k`, and the divided-difference
denominators evaluate to `(-1)^j q^{C(j,2) + j(k-j)} (q;q)_j (q;q)_{k-j}` (note
`C(j,2) + j(k-j) = jk - C(j+1,2)`), which is the explicit geometric Newton formula.

## Main declarations

* `newtonCoeff`, `newtonCoeff_eq` (the triangular reconstruction), `nodeNewtonPoly`.
* `eval_nodeNewtonPoly`: `P_n(v_i) = y_i`, needing only that `v_i` differs from the earlier nodes.
* `nodeNewtonPoly_eq_interpolate`, `eq_nodeNewtonPoly_of_eval_eq`: uniqueness.
* `newtonInterpolant` and the `newtonPoly_...` theorems: compatibility names
  for the same node-interpolation API.
* `newtonCoeff_eq_sum`: the divided-difference formula.
* `nodal_range_pow`, `prod_erase_pow_sub_pow`, `newtonCoeff_pow_eq_sum`: the geometric grid.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Polynomial Finset Lagrange

variable {F : Type*} [Field F]

/-- **Newton coefficients** by triangular elimination:
`c_k = (y_k - ∑_{r<k} c_r ∏_{j<r} (v_k - v_j)) / ∏_{j<k} (v_k - v_j)`. -/
noncomputable def newtonCoeff (v y : ℕ → F) (k : ℕ) : F :=
  (y k - ∑ r : Fin k, newtonCoeff v y r * ∏ j ∈ range (r : ℕ), (v k - v j)) /
    ∏ j ∈ range k, (v k - v j)
termination_by k
decreasing_by all_goals exact r.isLt

/-- **Triangular reconstruction** of the Newton coefficients. -/
theorem newtonCoeff_eq (v y : ℕ → F) (k : ℕ) :
    newtonCoeff v y k =
      (y k - ∑ r ∈ range k, newtonCoeff v y r * ∏ j ∈ range r, (v k - v j)) /
        ∏ j ∈ range k, (v k - v j) := by
  rw [newtonCoeff,
    Fin.sum_univ_eq_sum_range (fun r => newtonCoeff v y r * ∏ j ∈ range r, (v k - v j)) k]

/-- `c_0 = y_0`. -/
theorem newtonCoeff_zero (v y : ℕ → F) : newtonCoeff v y 0 = y 0 := by
  rw [newtonCoeff_eq]
  simp

/-- The triangular step, multiplied out. -/
theorem newtonCoeff_mul_prod (v y : ℕ → F) {k : ℕ} (hk : ∏ j ∈ range k, (v k - v j) ≠ 0) :
    newtonCoeff v y k * ∏ j ∈ range k, (v k - v j) =
      y k - ∑ r ∈ range k, newtonCoeff v y r * ∏ j ∈ range r, (v k - v j) := by
  rw [newtonCoeff_eq, div_mul_cancel₀ _ hk]

/-- **The Newton polynomial** `P_n = ∑_{k≤n} c_k ∏_{j<k} (X - v_j)`. -/
noncomputable def nodeNewtonPoly (v y : ℕ → F) (n : ℕ) : F[X] :=
  ∑ k ∈ range (n + 1), C (newtonCoeff v y k) * nodal (range k) v

/-- `P_{n+1} = P_n + c_{n+1} ∏_{j≤n} (X - v_j)`. -/
theorem nodeNewtonPoly_succ (v y : ℕ → F) (n : ℕ) :
    nodeNewtonPoly v y (n + 1) =
      nodeNewtonPoly v y n + C (newtonCoeff v y (n + 1)) * nodal (range (n + 1)) v :=
  sum_range_succ _ _

/-- **Newton interpolation**: `P_n(v_i) = y_i` for `i ≤ n`, provided `v_i` differs from the
earlier nodes `v_0, …, v_{i-1}`. -/
theorem eval_nodeNewtonPoly (v y : ℕ → F) {n i : ℕ} (hi : i ≤ n)
    (hne : ∏ j ∈ range i, (v i - v j) ≠ 0) : (nodeNewtonPoly v y n).eval (v i) = y i := by
  unfold nodeNewtonPoly
  rw [eval_finsetSum]
  simp only [eval_mul, eval_C, eval_nodal]
  rw [← sum_range_add_sum_Ico _ (Nat.succ_le_succ hi), sum_range_succ,
    sum_eq_zero (s := Ico (i + 1) (n + 1)) (fun k hk => ?_), add_zero,
    newtonCoeff_mul_prod v y hne]
  · ring
  · rw [mem_Ico] at hk
    rw [prod_eq_zero (mem_range.mpr (by omega : i < k)) (sub_self _), mul_zero]

/-- `deg P_n ≤ n`. -/
theorem degree_nodeNewtonPoly_lt (v y : ℕ → F) (n : ℕ) :
    (nodeNewtonPoly v y n).degree < (n + 1 : ℕ) := by
  unfold nodeNewtonPoly
  refine (degree_sum_le _ _).trans_lt ?_
  rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
  intro k hk
  calc (C (newtonCoeff v y k) * nodal (range k) v).degree
      ≤ (C (newtonCoeff v y k)).degree + (nodal (range k) v).degree := degree_mul_le _ _
    _ ≤ 0 + (k : WithBot ℕ) := add_le_add degree_C_le (by rw [degree_nodal, card_range])
    _ < (n + 1 : ℕ) := by
        rw [zero_add]
        exact WithBot.coe_lt_coe.mpr (mem_range.mp hk)

/-- For distinct nodes, the Newton polynomial is the Lagrange interpolant. -/
theorem nodeNewtonPoly_eq_interpolate (v y : ℕ → F) {n : ℕ}
    (hvs : Set.InjOn v (range (n + 1))) :
    nodeNewtonPoly v y n = interpolate (range (n + 1)) v y := by
  refine eq_interpolate_of_eval_eq y hvs ?_ fun i hi => ?_
  · rw [card_range]
    exact degree_nodeNewtonPoly_lt v y n
  · have hi' : i < n + 1 := mem_range.mp hi
    refine eval_nodeNewtonPoly v y (Nat.lt_succ_iff.mp hi') (prod_ne_zero_iff.mpr fun j hj => ?_)
    have hj' : j < i := mem_range.mp hj
    refine sub_ne_zero.mpr fun h => ?_
    have hij : i = j :=
      hvs (mem_coe.mpr (mem_range.mpr (by omega))) (mem_coe.mpr (mem_range.mpr (by omega))) h
    omega

/-- **Uniqueness**: a polynomial of degree `≤ n` taking the values `y_i` at `n+1` distinct
nodes `v_i` is the Newton polynomial. -/
theorem eq_nodeNewtonPoly_of_eval_eq (v y : ℕ → F) {n : ℕ}
    (hvs : Set.InjOn v (range (n + 1)))
    {P : F[X]} (hP : P.degree < (n + 1 : ℕ))
    (heval : ∀ i ∈ range (n + 1), P.eval (v i) = y i) : P = nodeNewtonPoly v y n := by
  rw [nodeNewtonPoly_eq_interpolate v y hvs]
  exact eq_interpolate_of_eval_eq y hvs (by rwa [card_range]) heval

/-- The top coefficient of `P_n` is `c_n`. -/
theorem coeff_nodeNewtonPoly_self (v y : ℕ → F) (n : ℕ) :
    (nodeNewtonPoly v y n).coeff n = newtonCoeff v y n := by
  unfold nodeNewtonPoly
  rw [finsetSum_coeff, sum_range_succ, sum_eq_zero (s := range n) (fun k hk => ?_), zero_add,
    coeff_C_mul]
  · have h := (nodal_monic (s := range n) (v := v)).coeff_natDegree
    rw [natDegree_nodal, card_range] at h
    rw [h, mul_one]
  · rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt, mul_zero]
    rw [natDegree_nodal, card_range]
    exact mem_range.mp hk

/-! ## Compatibility names for the interpolant API -/

/-- Compatibility alias for `nodeNewtonPoly`.  The node-qualified name avoids
the pre-existing scalar `newtonPoly` in `NewtonBasisGeneratingFunction`, while
this name preserves the interpolation API. -/
noncomputable def newtonInterpolant (v y : ℕ → F) (n : ℕ) : F[X] :=
  nodeNewtonPoly v y n

/-- Compatibility form of `nodeNewtonPoly_succ`. -/
theorem newtonPoly_succ (v y : ℕ → F) (n : ℕ) :
    newtonInterpolant v y (n + 1) =
      newtonInterpolant v y n + C (newtonCoeff v y (n + 1)) * nodal (range (n + 1)) v := by
  simpa only [newtonInterpolant] using nodeNewtonPoly_succ v y n

/-- Compatibility form of `eval_nodeNewtonPoly`. -/
theorem eval_newtonPoly (v y : ℕ → F) {n i : ℕ} (hi : i ≤ n)
    (hne : ∏ j ∈ range i, (v i - v j) ≠ 0) : (newtonInterpolant v y n).eval (v i) = y i := by
  simpa only [newtonInterpolant] using eval_nodeNewtonPoly v y hi hne

/-- Compatibility form of `degree_nodeNewtonPoly_lt`. -/
theorem degree_newtonPoly_lt (v y : ℕ → F) (n : ℕ) :
    (newtonInterpolant v y n).degree < (n + 1 : ℕ) := by
  simpa only [newtonInterpolant] using degree_nodeNewtonPoly_lt v y n

/-- Compatibility form of `nodeNewtonPoly_eq_interpolate`. -/
theorem newtonPoly_eq_interpolate (v y : ℕ → F) {n : ℕ}
    (hvs : Set.InjOn v (range (n + 1))) :
    newtonInterpolant v y n = interpolate (range (n + 1)) v y := by
  simpa only [newtonInterpolant] using nodeNewtonPoly_eq_interpolate v y hvs

/-- Compatibility form of `eq_nodeNewtonPoly_of_eval_eq`. -/
theorem eq_newtonPoly_of_eval_eq (v y : ℕ → F) {n : ℕ}
    (hvs : Set.InjOn v (range (n + 1)))
    {P : F[X]} (hP : P.degree < (n + 1 : ℕ))
    (heval : ∀ i ∈ range (n + 1), P.eval (v i) = y i) : P = newtonInterpolant v y n := by
  simpa only [newtonInterpolant] using eq_nodeNewtonPoly_of_eval_eq v y hvs hP heval

/-- Compatibility form of `coeff_nodeNewtonPoly_self`. -/
theorem coeff_newtonPoly_self (v y : ℕ → F) (n : ℕ) :
    (newtonInterpolant v y n).coeff n = newtonCoeff v y n := by
  simpa only [newtonInterpolant] using coeff_nodeNewtonPoly_self v y n

/-- **Newton's divided differences**: for distinct nodes,
`c_k = ∑_{j≤k} y_j / ∏_{r≤k, r≠j} (v_j - v_r)`. -/
theorem newtonCoeff_eq_sum (v y : ℕ → F) {k : ℕ} (hvs : Set.InjOn v (range (k + 1))) :
    newtonCoeff v y k =
      ∑ j ∈ range (k + 1), y j / ∏ r ∈ (range (k + 1)).erase j, (v j - v r) := by
  have h := coeff_eq_sum hvs (P := nodeNewtonPoly v y k)
    (by rw [card_range]; exact degree_nodeNewtonPoly_lt v y k)
  rw [card_range, Nat.add_sub_cancel, coeff_nodeNewtonPoly_self] at h
  rw [h, nodeNewtonPoly_eq_interpolate v y hvs]
  refine sum_congr rfl fun j hj => ?_
  rw [eval_interpolate_at_node _ hvs hj]

section Geometric

variable (q : F)

/-- The Newton basis on the geometric grid: `∏_{r<k} (X - q^r) = (-1)^k q^{C(k,2)} (X; q⁻¹)_k`. -/
theorem nodal_range_pow (hq : q ≠ 0) (k : ℕ) :
    nodal (range k) (fun j => q ^ j) =
      (-1) ^ k * C q ^ k.choose 2 * finiteQPochhammerIn X (C q⁻¹) k := by
  have hcq : (C q : F[X]) * C q⁻¹ = 1 := by rw [← C_mul, mul_inv_cancel₀ hq, C_1]
  have hfac : ∀ r : ℕ, (X : F[X]) - C q ^ r = (-1) * C q ^ r * (1 - X * C q⁻¹ ^ r) := by
    intro r
    have h : (C q : F[X]) ^ r * C q⁻¹ ^ r = 1 := by rw [← mul_pow, hcq, one_pow]
    linear_combination (-X) * h
  rw [nodal_eq, finiteQPochhammerIn]
  simp only [C_pow]
  rw [prod_congr rfl fun r _ => hfac r, prod_mul_distrib, prod_mul_distrib, prod_const,
    card_range, prod_pow_eq_pow_sum, sum_range_id, Nat.choose_two_right]

/-- The divided-difference denominators on the geometric grid:
`∏_{r≤k, r≠j} (q^j - q^r) = (-1)^j q^{C(j,2) + j(k-j)} (q;q)_j (q;q)_{k-j}`. -/
theorem prod_erase_pow_sub_pow {j k : ℕ} (hjk : j ≤ k) :
    ∏ r ∈ (range (k + 1)).erase j, (q ^ j - q ^ r) =
      (-1) ^ j * q ^ (j.choose 2 + j * (k - j)) *
        (finiteQPochhammerIn q q j * finiteQPochhammerIn q q (k - j)) := by
  have hsplit : (range (k + 1)).erase j = range j ∪ Ico (j + 1) (k + 1) := by
    ext r
    simp only [mem_erase, mem_range, mem_union, mem_Ico]
    omega
  have hdisj : Disjoint (range j) (Ico (j + 1) (k + 1)) := by
    rw [disjoint_left]
    intro r hr hr'
    simp only [mem_range, mem_Ico] at hr hr'
    omega
  have hlow : ∏ r ∈ range j, (q ^ j - q ^ r) =
      (-1) ^ j * q ^ j.choose 2 * finiteQPochhammerIn q q j := by
    have h1 : ∀ r ∈ range j, q ^ j - q ^ r = (-1) * q ^ r * (1 - q ^ (j - r)) := by
      intro r hr
      have hqj : q ^ j = q ^ r * q ^ (j - r) := by
        rw [← pow_add, Nat.add_sub_cancel' (mem_range.mp hr).le]
      rw [hqj]
      ring
    rw [prod_congr rfl h1, prod_mul_distrib, prod_mul_distrib, prod_const, card_range,
      prod_pow_eq_pow_sum, sum_range_id, ← Nat.choose_two_right, finiteQPochhammerIn]
    congr 1
    rw [← prod_range_reflect (fun i => 1 - q * q ^ i) j]
    refine prod_congr rfl fun r hr => ?_
    have hr' : r < j := mem_range.mp hr
    rw [← pow_succ', show j - 1 - r + 1 = j - r by omega]
  have hhigh : ∏ r ∈ Ico (j + 1) (k + 1), (q ^ j - q ^ r) =
      q ^ (j * (k - j)) * finiteQPochhammerIn q q (k - j) := by
    rw [prod_Ico_eq_prod_range, show k + 1 - (j + 1) = k - j by omega]
    have h2 : ∀ i ∈ range (k - j), q ^ j - q ^ (j + 1 + i) = q ^ j * (1 - q * q ^ i) := by
      intro i _
      rw [pow_add, pow_succ]
      ring
    rw [prod_congr rfl h2, prod_mul_distrib, prod_const, card_range, ← pow_mul,
      finiteQPochhammerIn]
  rw [hsplit, prod_union hdisj, hlow, hhigh, pow_add]
  ring

/-- **Geometric Newton interpolation**: on the nodes `1, q, …, q^k` the Newton coefficients are
`c_k = ∑_{j≤k} y_j / ((-1)^j q^{C(j,2) + j(k-j)} (q;q)_j (q;q)_{k-j})`. -/
theorem newtonCoeff_pow_eq_sum (y : ℕ → F) {k : ℕ}
    (hinj : Set.InjOn (fun j : ℕ => q ^ j) (range (k + 1))) :
    newtonCoeff (fun j => q ^ j) y k =
      ∑ j ∈ range (k + 1), y j / ((-1) ^ j * q ^ (j.choose 2 + j * (k - j)) *
        (finiteQPochhammerIn q q j * finiteQPochhammerIn q q (k - j))) := by
  rw [newtonCoeff_eq_sum _ y hinj]
  exact sum_congr rfl fun j hj => by
    rw [← prod_erase_pow_sub_pow q (Nat.lt_succ_iff.mp (mem_range.mp hj))]

end Geometric

end Fabius
