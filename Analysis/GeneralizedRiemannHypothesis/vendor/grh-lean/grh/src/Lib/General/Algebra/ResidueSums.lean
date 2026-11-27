import Lib.DiscreteSeries.FlenstedJensen.Defs

/-!
# Sums of residues at simple real poles

This file computes sums of residues of rational functions whose denominator has simple real roots.
Let `p = nodal univ x` be the monic polynomial with the distinct roots `x i`. The residue of `F / p`
at `x i` is `F (x i) / p' (x i)`. This file also determines the sign of `p' (x i)` when the roots
are ordered.

## Main definitions and results

* `New.DiscreteSeries.sum_eval_div_eval_derivative_nodal` and
  `sum_eval_div_sub_mul_eval_derivative_nodal`: two sums of residues at simple poles.
* `New.DiscreteSeries.eval_derivative_nodal`: the derivative of `nodal univ x`, the monic
  polynomial with roots `x j`, at the root `x i` is the product of the `x i - x j` over `j ≠ i`.

## Relation to the literature

The residue sums rest on Lagrange interpolation.
-/

noncomputable section

section LagrangeWeights

open Finset Polynomial Lagrange

namespace New.DiscreteSeries

section Residues

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {x : ι → ℝ} {F : ℝ[X]}

/-- The derivative of `nodal univ x`, the monic polynomial with roots `x j`, at the root `x i` is
the product of the `x i - x j` over `j ≠ i`. -/
lemma eval_derivative_nodal (x : ι → ℝ) (i : ι) :
    (derivative (nodal univ x)).eval (x i) = ∏ j ∈ univ.erase i, (x i - x j) := by
  rw [eval_nodal_derivative_eval_node_eq (mem_univ i), eval_nodal]

/-- Let `p = nodal univ x` be the monic polynomial with the distinct roots `x i` and let `F` be
monic of smaller degree. The residues `F (x i) / p' (x i)` of `F / p` add up to `1` if
`deg F + 1 = deg p` and to `0` otherwise. -/
theorem sum_eval_div_eval_derivative_nodal (hx : Function.Injective x) (hF : F.Monic)
    (h_degree : F.natDegree < Fintype.card ι) :
    ∑ i : ι, F.eval (x i) / (derivative (nodal univ x)).eval (x i) =
      if F.natDegree + 1 = Fintype.card ι then 1 else 0 := by
  -- By Lagrange's formula the sum is the coefficient of `F` in degree `deg p - 1`.
  simp_rw [eval_derivative_nodal]
  rw [← coeff_eq_sum hx.injOn (degree_le_natDegree.trans_lt (Nat.cast_lt.2 h_degree)), card_univ]
  split_ifs with h_top
  · rw [← h_top, Nat.add_sub_cancel, hF.coeff_natDegree]
  · exact coeff_eq_zero_of_natDegree_lt (by lia)

/-- Let `p = nodal univ x` have the distinct roots `x i`, let `deg F < deg p` and let `c` not be a
root. The residues of `F / ((t - c) p)` at the roots of `p` add up to minus the residue
`F (c) / p (c)` at the only other pole. -/
theorem sum_eval_div_sub_mul_eval_derivative_nodal (hx : Function.Injective x) {c : ℝ}
    (hc : ∀ i : ι, c ≠ x i) (h_degree : F.natDegree < Fintype.card ι) :
    ∑ i : ι, F.eval (x i) / ((x i - c) * (derivative (nodal univ x)).eval (x i)) =
      -(F.eval c / (nodal univ x).eval c) := by
  -- This is the barycentric form of Lagrange's formula for `F (c)`.
  have h_value : F.eval c = (nodal univ x).eval c *
      ∑ i : ι, nodalWeight univ x i * (c - x i)⁻¹ * F.eval (x i) := by
    rw [← eval_interpolate_not_at_node _ fun i _ ↦ hc i,
      ← eq_interpolate hx.injOn (degree_le_natDegree.trans_lt (Nat.cast_lt.2 h_degree))]
  rw [h_value, mul_div_cancel_left₀ _ (eval_nodal_not_at_node fun i _ ↦ hc i), ← sum_neg_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  grind [nodalWeight_eq_eval_derivative_nodal (mem_univ i)]

end Residues

section Signs

variable {M : ℕ} {x : Fin M → ℝ}

private lemma prod_erase_eq_prod_Ioi_mul_prod_Iio (f : Fin M → ℝ) (i : Fin M) :
    ∏ j ∈ univ.erase i, f j = (∏ j ∈ Ioi i, f j) * ∏ j ∈ Iio i, f j := by
  rw [← prod_disjUnion (disjoint_Ioi_Iio i), Ioi_disjUnion_Iio, compl_singleton]

/-- For decreasing roots `x 0 > x 1 > …` of `p = nodal univ x` the number `p' (x i)` has the sign
`(-1) ^ i`. -/
lemma derivative_nodal_sign_of_strictAnti (hx : StrictAnti x) (i : Fin M) :
    0 < (-1) ^ (i : ℕ) * (derivative (nodal univ x)).eval (x i) := by
  -- The factors `x i - x j` with `j < i` are negative, and those with `j > i` are positive.
  have h_split : (-1) ^ (i : ℕ) * ∏ j ∈ univ.erase i, (x i - x j) =
      (∏ j ∈ Ioi i, (x i - x j)) * ∏ j ∈ Iio i, (x j - x i) := by
    rw [prod_erase_eq_prod_Ioi_mul_prod_Iio, ← Fin.card_Iio, mul_left_comm, ← prod_neg]
    simp_rw [neg_sub]
  rw [eval_derivative_nodal, h_split]
  exact mul_pos (prod_pos fun j hj ↦ sub_pos.2 (hx (mem_Ioi.1 hj)))
    (prod_pos fun j hj ↦ sub_pos.2 (hx (mem_Iio.1 hj)))

/-- For increasing roots `x 0 < … < x (M - 1)` of `p = nodal univ x` the number `p' (x i)` has the
sign `(-1) ^ (M - 1 - i)`. -/
lemma derivative_nodal_sign_of_strictMono (hx : StrictMono x) (i : Fin M) :
    0 < (-1) ^ (M - 1 - (i : ℕ)) * (derivative (nodal univ x)).eval (x i) := by
  -- The factors `x i - x j` with `j > i` are negative, and those with `j < i` are positive.
  have h_split : (-1) ^ (M - 1 - (i : ℕ)) * ∏ j ∈ univ.erase i, (x i - x j) =
      (∏ j ∈ Ioi i, (x j - x i)) * ∏ j ∈ Iio i, (x i - x j) := by
    rw [prod_erase_eq_prod_Ioi_mul_prod_Iio, ← Fin.card_Ioi, ← mul_assoc, ← prod_neg]
    simp_rw [neg_sub]
  rw [eval_derivative_nodal, h_split]
  exact mul_pos (prod_pos fun j hj ↦ sub_pos.2 (hx (mem_Ioi.1 hj)))
    (prod_pos fun j hj ↦ sub_pos.2 (hx (mem_Iio.1 hj)))

end Signs

end New.DiscreteSeries

end LagrangeWeights

end
