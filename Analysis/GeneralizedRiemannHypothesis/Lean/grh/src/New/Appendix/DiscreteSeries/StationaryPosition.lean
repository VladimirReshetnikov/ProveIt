import Lib.General.Algebra.ResidueSums
import Lib.Shimura.Uniformisation.HolomorphicFamilies
import New.Appendix.DiscreteSeries.Positions

/-!
# The stationary position

For weights `μ` and `μ'` on opposite sides of `0`, with alternating signs on each side, there is a
position `(v, i₀)` in which `μ` moves each vector `v_j` to `v_{j + 1}` for `j < j₀`, where
`j₀ = d + 1` is the number of vectors, and `i₀` compresses `μ` to `μ'`
(`IsSteep.exists_isStationary`). The weight `μ` is realized as multiplication by `t` on
polynomials, and the form as a sum of residues.

Throughout, `p = nodal univ μ` and `q = nodal univ μ'` are the monic polynomials with the roots
`μ i` and `μ' j`, and `q_j = nodal (univ.erase j) μ'` is `q / (t - μ' j)`. The roots are indexed
from `0`, the vectors `v₁, …, v_{j₀}` from `1`. The vector `polyVec μ μ' F` is written `[F]`, and
`alternatingSignForm x y` is written `⟨x, y⟩`.

Notions from other files:

* `l.lowestKType`: the highest weight of the lowest `K`-type for the doubled Harish-Chandra
  parameter `l = 2 λ : HCParam ε`, a vector of integers; `intDiagonal` turns it into a diagonal
  matrix.
* `IsSteep l B e`: on `X` the signs `ε` are `+1` and that weight is `0`; on `Fin L` the signs
  are `+, -, …` and the weight decreases strictly in `[-3 B, -B]`.
* `IsPosition ε η d v i₀`: the ranks differ by `2 d + 1`, the columns of `v` are independent, their
  products vanish except that the last column has norm `±1`, and `i₀` is an isometry into their
  orthogonal complement.
* `signMatrix ε` is the diagonal matrix of the signs `ε`, and `formAdjoint ε η A` is the adjoint
  `A†` for the hermitian forms with the signs `ε` and `η`.
-/

noncomputable section

open Finset Lagrange

namespace New.DiscreteSeries

section Polynomials

open Polynomial

variable {L L' d : ℕ} {μ : Fin L → ℝ} {μ' : Fin L' → ℝ} {D : ℝ}

/-- The reals `μ 0 > μ 1 > …`, the roots of `p = nodal univ μ`, lie below the reals
`μ' 0 < μ' 1 < …`, the roots of `q = nodal univ μ'`. -/
structure AreOppositeNodes (μ : Fin L → ℝ) (μ' : Fin L' → ℝ) : Prop where
  /-- The roots of `p` decrease. -/
  strictAnti : StrictAnti μ
  /-- The roots of `q` increase. -/
  strictMono : StrictMono μ'
  /-- Each root of `p` is below each root of `q`. -/
  lt (i : Fin L) (j : Fin L') : μ i < μ' j

/-- The vector `[F]` of a real polynomial `F`, with the coordinates
`F (μ i) |p' (μ i) q (μ i)| ^ (-1 / 2)`, where `p` and `q` are the monic polynomials with the roots
`μ i` and `μ' j`. -/
def polyVec (μ : Fin L → ℝ) (μ' : Fin L' → ℝ) (F : ℝ[X]) (i : Fin L) : ℝ :=
  F.eval (μ i) / √|(derivative (nodal univ μ)).eval (μ i) * (nodal univ μ').eval (μ i)|

/-- The factor `|p (μ' j) / q' (μ' j)| ^ (1 / 2)`, where `p` and `q` are the monic polynomials with
the roots `μ i` and `μ' j`. It is chosen to normalize the vector `[q / (t - μ' j)]`. -/
def isometryScale (μ : Fin L → ℝ) (μ' : Fin L' → ℝ) (j : Fin L') : ℝ :=
  √|(nodal univ μ).eval (μ' j) / (derivative (nodal univ μ')).eval (μ' j)|

/-- The bilinear form `x₀ y₀ - x₁ y₁ + …` with the alternating signs `+, -, …` on real vectors. -/
def alternatingSignForm (x y : Fin L → ℝ) : ℝ :=
  ∑ i : Fin L, (-1) ^ (i : ℕ) * (x i * y i)

lemma mul_polyVec (F : ℝ[X]) (i : Fin L) : μ i * polyVec μ μ' F i = polyVec μ μ' (X * F) i := by
  rw [polyVec, polyVec, eval_mul, eval_X, mul_div_assoc]

lemma pow_mul_polyVec (F : ℝ[X]) (a : ℕ) (i : Fin L) :
    μ i ^ a * polyVec μ μ' F i = polyVec μ μ' (X ^ a * F) i := by
  simp [polyVec, mul_div_assoc]

/-- The value of `∏ k, (t - μ' k)` at `a` is `a - μ' j` times the value of the product over
`k ≠ j`. -/
lemma eval_nodal_eq_mul_erase (j : Fin L') (a : ℝ) :
    (nodal univ μ').eval a = (a - μ' j) * (nodal (univ.erase j) μ').eval a := by
  simp [nodal_eq_mul_nodal_erase (mem_univ j)]

/-- Let `q = nodal univ μ'` and `q_j = q / (t - μ' j)`, and write `[F] = polyVec μ μ' F`. Then
`μ [q_j] = μ' j [q_j] + [q]` entrywise, since `t q_j = μ' j q_j + q`. -/
lemma mul_polyVec_erase (j : Fin L') (i : Fin L) :
    μ i * polyVec μ μ' (nodal (univ.erase j) μ') i =
      μ' j * polyVec μ μ' (nodal (univ.erase j) μ') i + polyVec μ μ' (nodal univ μ') i := by
  rw [polyVec, polyVec, eval_nodal_eq_mul_erase j]
  ring

namespace AreOppositeNodes

/-- As each `μ i` lies below the `L'` roots of `q = ∏ (t - μ' j)`, the number `q (μ i)` has the
sign `(-1) ^ L'`. -/
lemma neg_one_pow_mul_eval_nodal_pos (h : AreOppositeNodes μ μ') (i : Fin L) :
    0 < (-1) ^ L' * (nodal univ μ').eval (μ i) := by
  have h_neg : (-1) ^ L' * (nodal univ μ').eval (μ i) = ∏ j : Fin L', (μ' j - μ i) := by
    simp_rw [eval_nodal, ← neg_sub (μ i), prod_neg, card_fin]
  rw [h_neg]
  exact prod_pos fun j _ ↦ sub_pos.2 (h.lt i j)

lemma eval_nodal_ne_zero (h : AreOppositeNodes μ μ') (i : Fin L) : (nodal univ μ').eval (μ i) ≠ 0 :=
  right_ne_zero_of_mul (h.neg_one_pow_mul_eval_nodal_pos i).ne'

/-- If each `μ i` lies below each `μ' j`, then `nodal univ μ = ∏ i, (t - μ i)` takes a positive
value at each `μ' j`. -/
lemma eval_nodal_pos (h : AreOppositeNodes μ μ') (j : Fin L') : 0 < (nodal univ μ).eval (μ' j) := by
  simpa [eval_nodal] using prod_pos fun i (_ : i ∈ univ) ↦ sub_pos.2 (h.lt i j)

/-- For opposite nodes no entry of the vector `[q] = polyVec μ μ' q` of `q = ∏ (t - μ' j)` is zero:
it is `q (μ i)` divided by `|p' (μ i) q (μ i)| ^ (1 / 2)`, where `p = ∏ (t - μ i)`. -/
lemma polyVec_nodal_ne_zero (h : AreOppositeNodes μ μ') (i : Fin L) :
    polyVec μ μ' (nodal univ μ') i ≠ 0 := by
  have h_deriv : (derivative (nodal univ μ)).eval (μ i) ≠ 0 :=
    right_ne_zero_of_mul (derivative_nodal_sign_of_strictAnti h.strictAnti i).ne'
  simp [polyVec, h_deriv, h.eval_nodal_ne_zero i]

/-- Let the decreasing reals `μ i`, the roots of `p = nodal univ μ`, lie below the `L'` increasing
roots `μ' j` of `q = nodal univ μ'`. Here `polyVec μ μ' F` is the vector with the entries
`F (μ i) |p' (μ i) q (μ i)| ^ (-1 / 2)`, and `alternatingSignForm x y` is the alternating sum
`∑ i, (-1) ^ i x i y i`. For the vectors of `F₁` and `F₂` it is `(-1) ^ L'` times the sum of the
residues of `F₁ F₂ / (p q)` at the roots of `p`. -/
lemma alternatingSignForm_polyVec (h : AreOppositeNodes μ μ') (F₁ F₂ : ℝ[X]) :
    alternatingSignForm (polyVec μ μ' F₁) (polyVec μ μ' F₂) =
      (-1) ^ L' * ∑ i : Fin L, (F₁ * F₂).eval (μ i) /
        ((derivative (nodal univ μ)).eval (μ i) * (nodal univ μ').eval (μ i)) := by
  rw [alternatingSignForm, mul_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  -- The sign of `w = p' (μ i) q (μ i)` is `(-1) ^ i (-1) ^ L'`.
  set w : ℝ := (derivative (nodal univ μ)).eval (μ i) * (nodal univ μ').eval (μ i) with hw
  have h_sign : 0 < (-1) ^ (i : ℕ) * (-1) ^ L' * w := by
    rw [hw, mul_mul_mul_comm]
    exact mul_pos (derivative_nodal_sign_of_strictAnti h.strictAnti i)
      (h.neg_one_pow_mul_eval_nodal_pos i)
  have h_abs : |w| = (-1) ^ (i : ℕ) * (-1) ^ L' * w := by
    simpa [abs_mul] using abs_of_pos h_sign
  have hw_ne : w ≠ 0 := right_ne_zero_of_mul h_sign.ne'
  calc
    (-1) ^ (i : ℕ) * (polyVec μ μ' F₁ i * polyVec μ μ' F₂ i)
        = (-1) ^ (i : ℕ) * ((F₁ * F₂).eval (μ i) / |w|) := by
      rw [polyVec, polyVec, ← hw, div_mul_div_comm, Real.mul_self_sqrt (abs_nonneg w), eval_mul]
    _ = (-1) ^ L' * ((F₁ * F₂).eval (μ i) / w) := by
      rw [h_abs]
      field_simp
      simp [← pow_mul]

/-- Let the decreasing roots `μ i` of `p = nodal univ μ` lie below the `L'` increasing roots `μ' j`
of `q = nodal univ μ'`. Here `polyVec μ μ' G` is the vector with the entries
`G (μ i) |p' (μ i) q (μ i)| ^ (-1 / 2)`, and `alternatingSignForm x y` is the alternating sum
`∑ i, (-1) ^ i x i y i`. For the vectors of `F` and `t ^ a q` it is `(-1) ^ L'` times the sum of
the residues of `t ^ a F / p`. -/
lemma alternatingSignForm_polyVec_X_pow_mul (h : AreOppositeNodes μ μ') (F : ℝ[X]) (a : ℕ) :
    alternatingSignForm (polyVec μ μ' F) (polyVec μ μ' (X ^ a * nodal univ μ')) =
      (-1) ^ L' *
        ∑ i : Fin L, (X ^ a * F).eval (μ i) / (derivative (nodal univ μ)).eval (μ i) := by
  have h_quotient (i : Fin L) : (F * (X ^ a * nodal univ μ')).eval (μ i) /
      ((derivative (nodal univ μ)).eval (μ i) * (nodal univ μ').eval (μ i)) =
      (X ^ a * F).eval (μ i) / (derivative (nodal univ μ)).eval (μ i) := by
    rw [← mul_assoc, eval_mul, mul_div_mul_right _ _ (h.eval_nodal_ne_zero i), mul_comm F]
  simp_rw [h.alternatingSignForm_polyVec, h_quotient]

/-- Let the `L` decreasing roots `μ i` of `p = nodal univ μ` lie below the `L'` increasing roots
`μ' j` of `q = nodal univ μ'`, where `L = L' + 2 d + 1`. Here `polyVec μ μ' F` is the vector with
the entries `F (μ i) |p' (μ i) q (μ i)| ^ (-1 / 2)`, and `alternatingSignForm x y` is the
alternating sum `∑ i, (-1) ^ i x i y i`. For the vectors of `t ^ a q` and `t ^ b q` with
`a + b ≤ 2 d` it is `(-1) ^ L'` if `a + b = 2 d` and `0` otherwise. -/
lemma alternatingSignForm_polyVec_X_pow_mul_X_pow_mul (h : AreOppositeNodes μ μ')
    (hL : L = L' + 2 * d + 1) {a b : ℕ} (hab : a + b ≤ 2 * d) :
    alternatingSignForm (polyVec μ μ' (X ^ a * nodal univ μ'))
      (polyVec μ μ' (X ^ b * nodal univ μ')) =
      if a + b = 2 * d then (-1) ^ L' else 0 := by
  have h_degree : (X ^ (b + a) * nodal univ μ').natDegree = b + a + L' := by
    simp [(monic_X_pow _).natDegree_mul nodal_monic]
  have h_lt : (X ^ (b + a) * nodal univ μ').natDegree < Fintype.card (Fin L) := by
    rw [h_degree, Fintype.card_fin]
    lia
  have h_top : b + a + L' + 1 = L ↔ a + b = 2 * d := by lia
  rw [h.alternatingSignForm_polyVec_X_pow_mul, ← mul_assoc, ← pow_add,
    sum_eval_div_eval_derivative_nodal h.strictAnti.injective ((monic_X_pow _).mul nodal_monic)
      h_lt, h_degree]
  simp [h_top]

/-- Let the `L` decreasing roots `μ i` of `p = nodal univ μ` lie below the `L'` increasing roots
`μ' j` of `q = nodal univ μ'`, where `L = L' + 2 d + 1`, and let `q_j = q / (t - μ' j)`. Here
`polyVec μ μ' F` is the vector with the entries `F (μ i) |p' (μ i) q (μ i)| ^ (-1 / 2)`, and
`alternatingSignForm x y` is the alternating sum `∑ i, (-1) ^ i x i y i`. For the vectors of `q_j`
and `t ^ a q` with `a ≤ 2 d` it is `0`: the residues of `t ^ a q_j / p` add up to `0`, as the
numerator has degree below `L - 1`. -/
lemma alternatingSignForm_polyVec_erase_X_pow_mul (h : AreOppositeNodes μ μ')
    (hL : L = L' + 2 * d + 1) (j : Fin L') {a : ℕ} (ha : a ≤ 2 * d) :
    alternatingSignForm (polyVec μ μ' (nodal (univ.erase j) μ'))
      (polyVec μ μ' (X ^ a * nodal univ μ')) =
      0 := by
  have hL' : 0 < L' := j.pos
  have h_degree : (X ^ a * nodal (univ.erase j) μ').natDegree = a + (L' - 1) := by
    simp [(monic_X_pow _).natDegree_mul nodal_monic]
  have h_lt : (X ^ a * nodal (univ.erase j) μ').natDegree < Fintype.card (Fin L) := by
    rw [h_degree, Fintype.card_fin]
    lia
  have h_not_top : a + (L' - 1) + 1 ≠ L := by lia
  rw [h.alternatingSignForm_polyVec_X_pow_mul,
    sum_eval_div_eval_derivative_nodal h.strictAnti.injective ((monic_X_pow _).mul nodal_monic)
      h_lt, h_degree]
  simp [h_not_top]

/-- Let the `L` decreasing roots `μ i` of `p = nodal univ μ` lie below the `L'` increasing roots
`μ' j` of `q = nodal univ μ'`, where `L = L' + 2 d + 1`, and let `q_j = q / (t - μ' j)`. Here
`polyVec μ μ' F` is the vector with the entries `F (μ i) |p' (μ i) q (μ i)| ^ (-1 / 2)`, and
`alternatingSignForm x y` is the alternating sum `∑ i, (-1) ^ i x i y i`. For the vectors of `q_j`
and `q_j'` it is `0` if `j ≠ j'`, and `(-1) ^ (L' + 1) q' (μ' j) / p (μ' j)` if `j = j'`: the
quotient `q_j / ((t - μ' j') p)` has a pole besides the roots of `p` only when `j = j'`. -/
lemma alternatingSignForm_polyVec_nodal_erase (h : AreOppositeNodes μ μ') (hL : L = L' + 2 * d + 1)
    (j j' : Fin L') :
    alternatingSignForm (polyVec μ μ' (nodal (univ.erase j) μ'))
      (polyVec μ μ' (nodal (univ.erase j') μ')) =
      if j = j' then
        (-1) ^ (L' + 1) * ((derivative (nodal univ μ')).eval (μ' j) / (nodal univ μ).eval (μ' j))
      else 0 := by
  have h_quotient (i : Fin L) : (nodal (univ.erase j) μ' * nodal (univ.erase j') μ').eval (μ i) /
      ((derivative (nodal univ μ)).eval (μ i) * (nodal univ μ').eval (μ i)) =
      (nodal (univ.erase j) μ').eval (μ i) /
        ((μ i - μ' j') * (derivative (nodal univ μ)).eval (μ i)) := by
    rw [eval_mul, eval_nodal_eq_mul_erase j', ← mul_assoc,
      mul_div_mul_right _ _ (eval_nodal_not_at_node fun k _ ↦ (h.lt i k).ne), mul_comm]
  have h_degree : (nodal (univ.erase j) μ').natDegree < Fintype.card (Fin L) := by
    rw [natDegree_nodal, card_erase_of_mem (mem_univ j), card_fin, Fintype.card_fin]
    lia
  simp_rw [h.alternatingSignForm_polyVec, h_quotient]
  rw [sum_eval_div_sub_mul_eval_derivative_nodal h.strictAnti.injective (fun i ↦ (h.lt i j').ne')
    h_degree]
  split_ifs with hj
  · simp [← hj, eval_nodal_derivative_eval_node_eq, pow_succ]
  · simp [eval_nodal_at_node (mem_erase_of_ne_of_mem (Ne.symm hj) (mem_univ j'))]

/-- Let the `L` decreasing roots `μ i` of `p = nodal univ μ` lie below the `L'` increasing roots
`μ' j` of `q = nodal univ μ'`, where `L = L' + 2 d + 1`, and let `q_j = q / (t - μ' j)`. The vectors
of the `q_j`, each scaled by `isometryScale μ μ' j = |p (μ' j) / q' (μ' j)| ^ (1 / 2)`, are
orthogonal for `alternatingSignForm`, and the vector of index `j` has the norm `(-1) ^ j`. -/
lemma isometryScale_mul_alternatingSignForm (h : AreOppositeNodes μ μ') (hL : L = L' + 2 * d + 1)
    (j j' : Fin L') :
    isometryScale μ μ' j * isometryScale μ μ' j' *
      alternatingSignForm (polyVec μ μ' (nodal (univ.erase j) μ'))
        (polyVec μ μ' (nodal (univ.erase j') μ')) =
      if j = j' then (-1) ^ (j : ℕ) else 0 := by
  rw [h.alternatingSignForm_polyVec_nodal_erase hL]
  obtain hj | rfl := ne_or_eq j j'
  · rw [ite_eq_right hj, ite_eq_right hj, mul_zero]
  -- `P = p (μ' j)` is positive and `Q = q' (μ' j)` has the sign `(-1) ^ (L' - 1 - j)`.
  set P : ℝ := (nodal univ μ).eval (μ' j) with hP
  set Q : ℝ := (derivative (nodal univ μ')).eval (μ' j) with hQ

  have hP_pos : 0 < P := h.eval_nodal_pos j
  have hQ_sign : 0 < (-1) ^ (L' - 1 - (j : ℕ)) * Q :=
    derivative_nodal_sign_of_strictMono h.strictMono j
  have hQ_ne : Q ≠ 0 := right_ne_zero_of_mul hQ_sign.ne'
  have hQ_abs : |Q| = (-1) ^ (L' - 1 - (j : ℕ)) * Q := by
    simpa [abs_mul] using abs_of_pos hQ_sign
  have h_scale : isometryScale μ μ' j * isometryScale μ μ' j =
      P / ((-1) ^ (L' - 1 - (j : ℕ)) * Q) := by
    rw [isometryScale, ← hP, ← hQ, Real.mul_self_sqrt (abs_nonneg _), abs_div, abs_of_pos hP_pos,
      hQ_abs]
  have h_parity : (-1 : ℝ) ^ (L' + 1) = (-1) ^ (L' - 1 - (j : ℕ)) * (-1) ^ (j : ℕ) := by
    rw [show L' + 1 = L' - 1 - (j : ℕ) + (j : ℕ) + 2 by lia, pow_add, neg_one_sq, mul_one, pow_add]
  rw [ite_eq_left rfl, ite_eq_left rfl, h_scale, h_parity]
  field_simp

end AreOppositeNodes

/-- Any two of the reals `μ i` and `μ' j`, the roots of `p = nodal univ μ` and `q = nodal univ μ'`,
differ by at least `1`, and each `μ i` is within `D ≥ 1` of `0` and of every `μ' j`. -/
structure AreSeparatedNodes (μ : Fin L → ℝ) (μ' : Fin L' → ℝ) (D : ℝ) : Prop where
  /-- The bound is at least `1`. -/
  one_le : 1 ≤ D
  /-- Two roots of `p` differ by at least `1`. -/
  pairwise_left : Pairwise fun i j : Fin L ↦ 1 ≤ |μ i - μ j|
  /-- Two roots of `q` differ by at least `1`. -/
  pairwise_right : Pairwise fun i j : Fin L' ↦ 1 ≤ |μ' i - μ' j|
  /-- A root of `p` and a root of `q` differ by at least `1`. -/
  one_le_abs_sub (i : Fin L) (j : Fin L') : 1 ≤ |μ i - μ' j|
  /-- A root of `p` and a root of `q` differ by at most `D`. -/
  abs_sub_le (i : Fin L) (j : Fin L') : |μ i - μ' j| ≤ D
  /-- The roots of `p` have modulus at most `D`. -/
  abs_le (i : Fin L) : |μ i| ≤ D

/-- If the roots `μ i` of `p = ∏ (t - μ i)` differ by at least `1`, then `|p' (μ i)| ≥ 1`, as
`p' (μ i)` is the product of the differences `μ i - μ j` over `j ≠ i`. -/
lemma one_le_abs_derivative_nodal (hμ : Pairwise fun i j : Fin L ↦ 1 ≤ |μ i - μ j|) (i : Fin L) :
    1 ≤ |(derivative (nodal univ μ)).eval (μ i)| := by
  simpa [eval_derivative_nodal, abs_prod] using
    one_le_prod₀ fun j (hj : j ∈ univ.erase i) ↦ hμ (ne_of_mem_erase hj).symm

/-- If `a` is within `D ≥ 1` of each of the `L` nodes `μ i`, the value at `a` of
`nodal s μ = ∏ i ∈ s, (t - μ i)` has modulus at most `D ^ L`. -/
lemma abs_eval_nodal_le {s : Finset (Fin L)} {a : ℝ} (hD : 1 ≤ D)
    (ha : ∀ i : Fin L, |a - μ i| ≤ D) : |(nodal s μ).eval a| ≤ D ^ L := by
  rw [eval_nodal, abs_prod]
  calc
    ∏ i ∈ s, |a - μ i| ≤ ∏ i ∈ s, D := prod_le_prod₀ (fun i _ ↦ abs_nonneg _) fun i _ ↦ ha i
    _ = D ^ #s := prod_const D
    _ ≤ D ^ L := pow_le_pow_right₀ hD (card_finset_fin_le s)

namespace AreSeparatedNodes

/-- Let `AreSeparatedNodes μ μ' D` hold: any two of the reals `μ i` and `μ' j` differ by at least
`1`, and each `μ i` is within `D ≥ 1` of `0` and of every `μ' j`. Let `p = nodal univ μ` and
`q = nodal univ μ'`. If `|G (μ i)| ≤ |q (μ i)|`, the square of the entry
`F (μ i) G (μ i) |p' (μ i) q (μ i)| ^ (-1 / 2)` of `polyVec μ μ' (F * G)` is at most
`F (μ i) ^ 2 |G (μ i)|`, as `|p' (μ i)| ≥ 1`. -/
lemma polyVec_sq_le (h : AreSeparatedNodes μ μ' D) {F G : ℝ[X]} {i : Fin L}
    (hG : |G.eval (μ i)| ≤ |(nodal univ μ').eval (μ i)|) :
    polyVec μ μ' (F * G) i ^ 2 ≤ F.eval (μ i) ^ 2 * |G.eval (μ i)| := by
  set w : ℝ := (derivative (nodal univ μ)).eval (μ i) * (nodal univ μ').eval (μ i) with hw
  have h_denominator : |G.eval (μ i)| ≤ |w| := by
    rw [hw, abs_mul]
    exact hG.trans (le_mul_of_one_le_left (abs_nonneg _)
      (one_le_abs_derivative_nodal h.pairwise_left i))
  calc
    polyVec μ μ' (F * G) i ^ 2 = F.eval (μ i) ^ 2 * |G.eval (μ i)| * (|G.eval (μ i)| / |w|) := by
      rw [polyVec, ← hw, div_pow, Real.sq_sqrt (abs_nonneg w), eval_mul, mul_pow,
        ← sq_abs (G.eval _)]
      ring
    _ ≤ F.eval (μ i) ^ 2 * |G.eval (μ i)| :=
      mul_le_of_le_one_right (by positivity) (div_le_one_of_le₀ h_denominator (abs_nonneg w))

/-- Let the roots `μ i` of `p = nodal univ μ` and `μ' j` of `q = nodal univ μ'` differ by at least
`1`, with each `μ i` within `D ≥ 1` of `0` and of the `μ' j`, and let `L = L' + 2 d + 1`. For
`a ≤ 2 d` the entry `(μ i) ^ a q (μ i) |p' (μ i) q (μ i)| ^ (-1 / 2)` of the vector
`polyVec μ μ' (X ^ a * q)` has modulus at most `D ^ a |q (μ i)| ^ (1 / 2) ≤ D ^ L`. -/
lemma abs_polyVec_le (h : AreSeparatedNodes μ μ' D) (hL : L = L' + 2 * d + 1) {a : ℕ}
    (ha : a ≤ 2 * d) (i : Fin L) :
    |polyVec μ μ' (X ^ a * nodal univ μ') i| ≤ D ^ L := by
  have hD : 0 ≤ D := zero_le_one.trans h.one_le
  refine abs_le_of_sq_le_sq ?_ (pow_nonneg hD L)
  calc
    polyVec μ μ' (X ^ a * nodal univ μ') i ^ 2
        ≤ (|μ i| ^ a) ^ 2 * |(nodal univ μ').eval (μ i)| := by
      rw [← abs_pow, sq_abs]
      simpa using h.polyVec_sq_le (F := X ^ a) le_rfl
    _ ≤ (D ^ a) ^ 2 * D ^ L' := by
      gcongr
      · exact h.abs_le i
      · exact abs_eval_nodal_le h.one_le (h.abs_sub_le i)
    _ ≤ (D ^ L) ^ 2 := by
      simpa [← pow_mul, ← pow_add] using pow_le_pow_right₀ h.one_le (by lia)

/-- Let the roots `μ i` of `p` and `μ' j` of `q` differ by at least `1`, with each `μ i` within
`D ≥ 1` of `0` and of the `μ' j`, and let `L = L' + 2 d + 1` and `q_j = q / (t - μ' j)`. The entry
`q_j (μ i) |p' (μ i) q (μ i)| ^ (-1 / 2)` of the vector `polyVec` of `q_j`, multiplied by
`isometryScale μ μ' j = |p (μ' j) / q' (μ' j)| ^ (1 / 2)`, has modulus at most
`|p (μ' j) q_j (μ i)| ^ (1 / 2) ≤ D ^ L`. -/
lemma abs_isometryScale_mul_le (h : AreSeparatedNodes μ μ' D) (hL : L = L' + 2 * d + 1)
    (j : Fin L') (i : Fin L) :
    |isometryScale μ μ' j * polyVec μ μ' (nodal (univ.erase j) μ') i| ≤ D ^ L := by
  have hD : 0 ≤ D := zero_le_one.trans h.one_le
  have h_scale : isometryScale μ μ' j ^ 2 ≤ |(nodal univ μ).eval (μ' j)| := by
    rw [isometryScale, Real.sq_sqrt (abs_nonneg _), abs_div]
    exact div_le_self (abs_nonneg _) (one_le_abs_derivative_nodal h.pairwise_right j)
  have h_erase : |(nodal (univ.erase j) μ').eval (μ i)| ≤ |(nodal univ μ').eval (μ i)| := by
    rw [eval_nodal_eq_mul_erase j, abs_mul]
    exact le_mul_of_one_le_left (abs_nonneg _) (h.one_le_abs_sub i j)
  have h_entry : polyVec μ μ' (nodal (univ.erase j) μ') i ^ 2 ≤
      |(nodal (univ.erase j) μ').eval (μ i)| := by
    simpa using h.polyVec_sq_le (F := 1) h_erase
  have h_left : |(nodal univ μ).eval (μ' j)| ≤ D ^ L :=
    abs_eval_nodal_le h.one_le fun k ↦ (abs_sub_comm (μ' j) (μ k)).trans_le (h.abs_sub_le k j)
  have h_right : |(nodal (univ.erase j) μ').eval (μ i)| ≤ D ^ L :=
    (abs_eval_nodal_le h.one_le (h.abs_sub_le i)).trans (pow_le_pow_right₀ h.one_le (by lia))
  refine abs_le_of_sq_le_sq ?_ (pow_nonneg hD L)
  calc
    (isometryScale μ μ' j * polyVec μ μ' (nodal (univ.erase j) μ') i) ^ 2
        ≤ |(nodal univ μ).eval (μ' j)| * |(nodal (univ.erase j) μ').eval (μ i)| := by
      rw [mul_pow]
      gcongr
    _ ≤ D ^ L * D ^ L := by gcongr
    _ = (D ^ L) ^ 2 := (sq _).symm

end AreSeparatedNodes

end Polynomials

section Matrices

open Matrix ComplexConjugate

variable {n m X : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype X]
  {ε : n → ℤˣ} {η : m → ℤˣ} {l : HCParam ε} {k : HCParam η} {L L' d : ℕ}
  {e : X ⊕ Fin L ≃ n} {e' : X ⊕ Fin L' ≃ m} {B D : ℝ} {μ : Fin L → ℝ} {μ' : Fin L' → ℝ}

/-- The matrix with the columns `v_{a + 1} = [t ^ a q]`, `a ≤ d`, where `q = nodal univ μ'` and
`[F] = polyVec μ μ' F`: through `e : X ⊕ Fin L ≃ n` the column has these coordinates on `Fin L` and
vanishes on `X`. -/
def positionVec (e : X ⊕ Fin L ≃ n) (μ : Fin L → ℝ) (μ' : Fin L' → ℝ) (d : ℕ) :
    Matrix n (Fin (d + 1)) ℂ :=
  (fromRows 0 (of fun (i : Fin L) (a : Fin (d + 1)) ↦
    (polyVec μ μ' (Polynomial.X ^ a.val * nodal univ μ') i : ℂ))).submatrix e.symm id

/-- The matrix `i₀` that, through `e` and `e'`, is `1` on `ℂ^X` and sends the `j`th of the other
basis vectors to the vector `[q_j]`, where `q_j = nodal (univ.erase j) μ'` and
`[F] = polyVec μ μ' F`, scaled by `isometryScale μ μ' j`. -/
def positionIsometry [DecidableEq X] (e : X ⊕ Fin L ≃ n) (e' : X ⊕ Fin L' ≃ m) (μ : Fin L → ℝ)
    (μ' : Fin L' → ℝ) : Matrix n m ℂ :=
  (fromBlocks 1 0 0 (of fun (i : Fin L) (j : Fin L') ↦
    (↑(isometryScale μ μ' j * polyVec μ μ' (nodal (univ.erase j) μ') i) : ℂ))).submatrix
    e.symm e'.symm

omit [Fintype n] [DecidableEq n] [Fintype X] in
/-- The columns of `positionVec e μ μ' d` vanish on the coordinates in `X`. -/
lemma positionVec_apply_inl (x : X) (a : Fin (d + 1)) :
    positionVec e μ μ' d (e (Sum.inl x)) a = 0 := by simp [positionVec]

omit [Fintype n] [DecidableEq n] [Fintype X] in
/-- At the coordinate `e (Sum.inr i)`, the column of index `a` of `positionVec e μ μ' d` equals the
`i`th entry of the real vector `polyVec μ μ' (X ^ a * q)`, where `q = nodal univ μ'`. -/
lemma positionVec_apply_inr (i : Fin L) (a : Fin (d + 1)) :
    positionVec e μ μ' d (e (Sum.inr i)) a =
      (polyVec μ μ' (Polynomial.X ^ a.val * nodal univ μ') i : ℂ) := by
  simp [positionVec]

omit [Fintype n] [Fintype m] [DecidableEq m] [Fintype X] in
/-- The matrix `i₀ = positionIsometry e e' μ μ'` is the identity on `ℂ^X`: its column of index
`e' (Sum.inl x)` is the basis vector of index `e (Sum.inl x)`. -/
lemma positionIsometry_apply_inl [DecidableEq X] (i : n) (x : X) :
    positionIsometry e e' μ μ' i (e' (Sum.inl x)) = if i = e (Sum.inl x) then 1 else 0 := by
  obtain ⟨x' | i, rfl⟩ := e.surjective i <;> simp [positionIsometry, one_apply]

omit [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype X] in
/-- For `j : Fin L'`, the column of index `e' (Sum.inr j)` of `positionIsometry e e' μ μ'` vanishes
on the coordinates `e (Sum.inl x)` with `x` in `X`. -/
lemma positionIsometry_apply_inl_inr [DecidableEq X] (x : X) (j : Fin L') :
    positionIsometry e e' μ μ' (e (Sum.inl x)) (e' (Sum.inr j)) = 0 := by simp [positionIsometry]

omit [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype X] in
/-- For `i : Fin L` and `j : Fin L'`, the entry of `positionIsometry e e' μ μ'` at
`(e (Sum.inr i), e' (Sum.inr j))` is `isometryScale μ μ' j` times the `i`th coordinate of
`polyVec μ μ' (nodal (univ.erase j) μ')`. -/
lemma positionIsometry_apply_inr_inr [DecidableEq X] (i : Fin L) (j : Fin L') :
    positionIsometry e e' μ μ' (e (Sum.inr i)) (e' (Sum.inr j)) =
      ((isometryScale μ μ' j * polyVec μ μ' (nodal (univ.erase j) μ') i : ℝ) : ℂ) := by
  simp [positionIsometry]

lemma alternatingSignForm_const_mul_left (c : ℝ) (x y : Fin L → ℝ) :
    alternatingSignForm (fun i : Fin L ↦ c * x i) y = c * alternatingSignForm x y := by
  simp [alternatingSignForm, mul_sum, mul_left_comm, mul_assoc]

lemma alternatingSignForm_const_mul_right (c : ℝ) (x y : Fin L → ℝ) :
    alternatingSignForm x (fun i : Fin L ↦ c * y i) = c * alternatingSignForm x y := by
  simp [alternatingSignForm, mul_sum, mul_left_comm]

omit [Fintype n] [DecidableEq n] [Fintype X] in
/-- Let the nodes differ by at least `1`, with each `μ i` within `D ≥ 1` of `0` and of the `μ' j`,
and let `L = L' + 2 d + 1`. The columns `[t ^ a q]`, `a ≤ d`, of `positionVec` have entries of norm
at most `D ^ L`. -/
lemma AreSeparatedNodes.norm_positionVec_le (h : AreSeparatedNodes μ μ' D)
    (hL : L = L' + 2 * d + 1) (i : n) (a : Fin (d + 1)) : ‖positionVec e μ μ' d i a‖ ≤ D ^ L := by
  obtain ⟨x | i, rfl⟩ := e.surjective i
  · simpa [positionVec_apply_inl] using pow_nonneg (zero_le_one.trans h.one_le) L
  · simpa [positionVec_apply_inr] using h.abs_polyVec_le hL (a := a.val) (by lia) i

omit [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype X] in
/-- Let the nodes differ by at least `1`, with each `μ i` within `D ≥ 1` of `0` and of the `μ' j`,
and let `L = L' + 2 d + 1`. The matrix `positionIsometry`, which is `1` on `ℂ^X` and has the scaled
vectors `[q_j]` as its other columns, has entries of norm at most `D ^ L`. -/
lemma AreSeparatedNodes.norm_positionIsometry_le [DecidableEq X] (h : AreSeparatedNodes μ μ' D)
    (hL : L = L' + 2 * d + 1) (i : n) (j : m) : ‖positionIsometry e e' μ μ' i j‖ ≤ D ^ L := by
  have h_one_le : 1 ≤ D ^ L := one_le_pow₀ h.one_le
  have h_nonneg : 0 ≤ D ^ L := zero_le_one.trans h_one_le
  obtain ⟨x' | j, rfl⟩ := e'.surjective j
  · classical
    rw [positionIsometry_apply_inl]
    split_ifs <;> simpa
  · obtain ⟨x | i, rfl⟩ := e.surjective i
    · rwa [positionIsometry_apply_inl_inr, norm_zero]
    · simpa [positionIsometry_apply_inr_inr] using h.abs_isometryScale_mul_le hL j i

/-- If `l` is steep, so that the signs `ε` are `+1` on `X` and alternate on `Fin L`, the hermitian
form with the matrix `signMatrix ε = diag ε`, taken on a column of `A` and a column of `A'`, is the
standard form on the coordinates in `X` plus the alternating form on the others. -/
lemma IsSteep.conjTranspose_mul_signMatrix_mul_apply {α β : Type} (hl : IsSteep l B e)
    (A : Matrix n α ℂ) (A' : Matrix n β ℂ) (a : α) (b : β) :
    (Aᴴ * signMatrix ε * A') a b =
      ∑ x : X, conj (A (e (Sum.inl x)) a) * A' (e (Sum.inl x)) b +
        ∑ i : Fin L, (-1) ^ i.val * (conj (A (e (Sum.inr i)) a) * A' (e (Sum.inr i)) b) := by
  rw [mul_apply, ← e.sum_comp, Fintype.sum_sum_type]
  simp [signMatrix, hl.sign_inl, hl.sign_inr, mul_comm, mul_left_comm]

/-- Let `l` be steep, so that through `e : X ⊕ Fin L ≃ n` the signs `ε` are `+1` on `X` and
`+, -, …` on `Fin L`. Let the column `a` of `A` vanish on `X` and have the real coordinates `f i`
on `Fin L`, and let the column `b` of `A'` have the real coordinates `g i` on `Fin L`. Then the
hermitian form with the matrix `signMatrix ε = diag ε` takes on the two columns the value
`alternatingSignForm f g = ∑ i, (-1) ^ i f i g i`. -/
lemma IsSteep.conjTranspose_mul_signMatrix_mul_apply_of_real {α β : Type} (hl : IsSteep l B e)
    {A : Matrix n α ℂ} {A' : Matrix n β ℂ} {a : α} {b : β} {f g : Fin L → ℝ}
    (hA_inl : ∀ x : X, A (e (Sum.inl x)) a = 0)
    (hA_inr : ∀ i : Fin L, A (e (Sum.inr i)) a = (f i : ℂ))
    (hA'_inr : ∀ i : Fin L, A' (e (Sum.inr i)) b = (g i : ℂ)) :
    (Aᴴ * signMatrix ε * A') a b = (alternatingSignForm f g : ℂ) := by
  rw [hl.conjTranspose_mul_signMatrix_mul_apply]
  simp [alternatingSignForm, hA_inl, hA_inr, hA'_inr]

omit [Fintype n] [Fintype X] [DecidableEq n] in
/-- If the nodes are opposite and `d < L`, the columns of `positionVec e μ μ' d` are linearly
independent over `ℂ`. -/
lemma AreOppositeNodes.linearIndependent_positionVec (h : AreOppositeNodes μ μ') (hd : d < L) :
    LinearIndependent ℂ (positionVec e μ μ' d).col := by
  refine Fintype.linearIndependent_iff.2 fun c hc ↦ ?_
  suffices h_zero : c = 0 from congrFun h_zero
  let node (j : Fin (d + 1)) : Fin L := j.castLE hd
  have h_inj : Function.Injective fun j : Fin (d + 1) ↦ (μ (node j) : ℂ) :=
    Complex.ofReal_injective.comp (h.strictAnti.injective.comp (Fin.castLE_injective hd))
  refine eq_zero_of_forall_index_sum_mul_pow_eq_zero h_inj fun j ↦ ?_
  have h_entry : (∑ a : Fin (d + 1), c a * (μ (node j) : ℂ) ^ a.val) *
      polyVec μ μ' (nodal univ μ') (node j) = 0 := by
    simpa [positionVec_apply_inr, ← pow_mul_polyVec, sum_mul, mul_assoc] using
      congrFun hc (e (Sum.inr (node j)))
  exact eq_zero_of_ne_zero_of_mul_right_eq_zero (mod_cast h.polyVec_nodal_ne_zero _) h_entry

/-- Let `l` be steep, so that the signs `ε` are `+1` on `X` and `+, -, …` on `Fin L`, let the
decreasing nodes `μ` lie below the increasing nodes `μ'`, and let `L = L' + 2 d + 1`. For the form
with the matrix `signMatrix ε = diag ε`, the products of the vectors `[t ^ a q]`, `a ≤ d`, vanish,
except that `[t ^ d q]` has the norm `(-1) ^ L'`. -/
lemma IsSteep.gram_positionVec (hl : IsSteep l B e) (h : AreOppositeNodes μ μ')
    (hL : L = L' + 2 * d + 1) (a b : Fin (d + 1)) :
    ((positionVec e μ μ' d)ᴴ * signMatrix ε * positionVec e μ μ' d) a b =
      if a.val + b.val = 2 * d then (-1) ^ L' else 0 := by
  have h_real : ((positionVec e μ μ' d)ᴴ * signMatrix ε * positionVec e μ μ' d) a b =
      (alternatingSignForm (polyVec μ μ' (Polynomial.X ^ a.val * nodal univ μ'))
        (polyVec μ μ' (Polynomial.X ^ b.val * nodal univ μ')) : ℂ) :=
    hl.conjTranspose_mul_signMatrix_mul_apply_of_real (positionVec_apply_inl · a)
      (positionVec_apply_inr · a) (positionVec_apply_inr · b)
  rw [h_real, h.alternatingSignForm_polyVec_X_pow_mul_X_pow_mul hL (by lia)]
  simp [apply_ite Complex.ofReal]

omit [Fintype m] [DecidableEq m] in
/-- If `l` is steep, the nodes are opposite and `L = L' + 2 d + 1`, the columns outside `X` of
`positionIsometry`, which are the scaled `[q_j] = polyVec μ μ' (q / (t - μ' j))`, are orthogonal
with the norms `+1, -1, …` for the form with the matrix `signMatrix ε`. -/
lemma IsSteep.gram_positionIsometry_inr [DecidableEq X]
    (hl : IsSteep l B e) (h : AreOppositeNodes μ μ') (hL : L = L' + 2 * d + 1) (j j' : Fin L') :
    ((positionIsometry e e' μ μ')ᴴ * signMatrix ε * positionIsometry e e' μ μ')
      (e' (Sum.inr j)) (e' (Sum.inr j')) = if j = j' then (-1) ^ j.val else 0 := by
  let w (j : Fin L') : Fin L → ℝ := polyVec μ μ' (nodal (univ.erase j) μ')
  let s : Fin L' → ℝ := isometryScale μ μ'
  have h_real : ((positionIsometry e e' μ μ')ᴴ * signMatrix ε * positionIsometry e e' μ μ')
      (e' (Sum.inr j)) (e' (Sum.inr j')) =
        (alternatingSignForm (fun i : Fin L ↦ s j * w j i) (fun i : Fin L ↦ s j' * w j' i) : ℂ) :=
    hl.conjTranspose_mul_signMatrix_mul_apply_of_real (positionIsometry_apply_inl_inr · j)
      (positionIsometry_apply_inr_inr · j) (positionIsometry_apply_inr_inr · j')
  rw [h_real, alternatingSignForm_const_mul_left, alternatingSignForm_const_mul_right, ← mul_assoc,
    h.isometryScale_mul_alternatingSignForm hL]
  simp [apply_ite Complex.ofReal]

/-- Let `l` be steep with respect to `B` and `e` (`IsSteep l B e`): the signs `ε` are `+1` on `X`,
where the weight of the lowest `K`-type is `0`, and `+, -, …` on `Fin L`, where that weight
decreases strictly in `[-3 B, -B]`. Let the signs `η` be `+1` on `X` and `+, -, …` on `Fin L'`,
where `L = L' + 2 d + 1`. Let the decreasing nodes `μ`, the roots of the monic polynomial `p`, lie
below the increasing nodes `μ'`, the roots of the monic polynomial `q`. For a polynomial `F` let
`[F] = polyVec μ μ' F` be the real vector with the entries `F (μ i) |p' (μ i) q (μ i)| ^ (-1 / 2)`.
The columns of `positionVec` are the vectors `[t ^ a q]`, `a ≤ d`, extended by `0` on `X`. The
matrix `i₀ = positionIsometry e e' μ μ'` is `1` on `ℂ^X`, and its column of index `e' (Sum.inr j)`
is `|p (μ' j) / q' (μ' j)| ^ (1 / 2)` times `[q / (t - μ' j)]`. These form a position of `U(η)` in
`U(ε)`: the ranks differ by `2 d + 1`, the vectors are independent with vanishing products except
that the last has norm `±1`, and `i₀` is an isometry into their orthogonal complement. -/
lemma IsSteep.isPosition [DecidableEq X]
    (hl : IsSteep l B e) (h : AreOppositeNodes μ μ') (hL : L = L' + 2 * d + 1)
    (h_pos : ∀ x : X, η (e' (Sum.inl x)) = 1)
    (h_alt : ∀ j : Fin L', η (e' (Sum.inr j)) = (-1) ^ j.val) :
    IsPosition ε η d (positionVec e μ μ' d) (positionIsometry e e' μ μ') where
  card_eq := by
    simp [← Fintype.card_congr e, ← Fintype.card_congr e', hL, add_assoc]
  independent := h.linearIndependent_positionVec (by lia)
  gram_eq_zero a b hab := by
    have h_ne : a.val + b.val ≠ 2 * d := by
      simp only [ne_eq, Fin.ext_iff, Fin.val_last] at hab
      lia
    rw [hl.gram_positionVec h hL, ite_eq_right h_ne]
  gram_last_eq_sign := by
    simpa [hl.gram_positionVec h hL, two_mul] using neg_one_pow_eq_or ℂ L'
  isometry := by
    ext j j'
    obtain ⟨x | j, rfl⟩ := e'.surjective j
    · rw [hl.conjTranspose_mul_signMatrix_mul_apply]
      obtain ⟨x' | j', rfl⟩ := e'.surjective j' <;>
        simp [positionIsometry_apply_inl, positionIsometry_apply_inl_inr, signMatrix,
          diagonal_apply, h_pos, eq_comm]
    · obtain ⟨x' | j', rfl⟩ := e'.surjective j'
      · rw [hl.conjTranspose_mul_signMatrix_mul_apply]
        simp [positionIsometry_apply_inl, positionIsometry_apply_inl_inr, signMatrix]
      · rw [hl.gram_positionIsometry_inr h hL]
        simp [signMatrix, diagonal_apply, h_alt]
  orthogonal := by
    ext j a
    obtain ⟨x | j, rfl⟩ := e'.surjective j
    · simp [hl.conjTranspose_mul_signMatrix_mul_apply, positionIsometry_apply_inl,
        positionVec_apply_inl]
    · have h_real : ((positionIsometry e e' μ μ')ᴴ * signMatrix ε * positionVec e μ μ' d)
          (e' (Sum.inr j)) a = (alternatingSignForm
            (fun i : Fin L ↦ isometryScale μ μ' j * polyVec μ μ' (nodal (univ.erase j) μ') i)
            (polyVec μ μ' (Polynomial.X ^ a.val * nodal univ μ')) : ℂ) :=
        hl.conjTranspose_mul_signMatrix_mul_apply_of_real (positionIsometry_apply_inl_inr · j)
          (positionIsometry_apply_inr_inr · j) (positionVec_apply_inr · a)
      rw [h_real, alternatingSignForm_const_mul_left,
        h.alternatingSignForm_polyVec_erase_X_pow_mul hL j (by lia)]
      simp

omit [Fintype X] in
/-- If the weight of the lowest `K`-type of `l` (`l.lowestKType`) is `μ` on `Fin L`, its diagonal
matrix `intDiagonal l.lowestKType` sends each of the first `d` columns `v_{a + 1} = [t ^ a q]` of
`positionVec` to the next column, as `μ [F] = [t F]`; `initCols` keeps these first `d` columns. -/
lemma intDiagonal_mul_positionVec (hμ : ∀ i : Fin L, (l.lowestKType (e (Sum.inr i)) : ℝ) = μ i) :
    intDiagonal l.lowestKType * initCols (positionVec e μ μ' d) =
      (positionVec e μ μ' d).submatrix id Fin.succ := by
  ext i a
  obtain ⟨x | i, rfl⟩ := e.surjective i
  · simp [initCols, positionVec_apply_inl]
  · have hi : (l.lowestKType (e (Sum.inr i)) : ℂ) = μ i := mod_cast hμ i
    simp [initCols, hi, positionVec_apply_inr, ← Complex.ofReal_mul, mul_polyVec, pow_succ',
      mul_assoc]

omit [Fintype X] in
/-- Let the nodes differ by at least `1`, with each `μ i` within `D ≥ 1` of `0` and of the `μ' j`,
let `L = L' + 2 d + 1`, and let the weight of the lowest `K`-type of `l`, acting as a diagonal
matrix, be `μ` on `Fin L`. The first column `v₁` of `positionVec` is `0` on `X` and has the entries
`q (μ i) |p' (μ i) q (μ i)| ^ (-1 / 2)` on `Fin L`. Then for `a ≤ 2 d` the entries of the `a`th
power of the diagonal matrix applied to `v₁`, which are those of `v₁` times `(μ i) ^ a`, have
modulus at most `D ^ L`. -/
lemma AreSeparatedNodes.norm_pow_mulVec_positionVec_le (h : AreSeparatedNodes μ μ' D)
    (hL : L = L' + 2 * d + 1) (hμ : ∀ i : Fin L, (l.lowestKType (e (Sum.inr i)) : ℝ) = μ i)
    {a : ℕ} (ha : a ≤ 2 * d) (i : n) :
    ‖(intDiagonal l.lowestKType ^ a *ᵥ (positionVec e μ μ' d).col 0) i‖ ≤ D ^ L := by
  obtain ⟨x | i, rfl⟩ := e.surjective i
  · simpa [diagonal_pow, mulVec_diagonal, positionVec_apply_inl] using
      pow_nonneg (zero_le_one.trans h.one_le) L
  · have hi : (l.lowestKType (e (Sum.inr i)) : ℂ) = μ i := mod_cast hμ i
    have h_bound : |μ i ^ a * polyVec μ μ' (nodal univ μ') i| ≤ D ^ L := by
      simpa [pow_mul_polyVec] using h.abs_polyVec_le hL ha i
    simpa [diagonal_pow, mulVec_diagonal, positionVec_apply_inr, hi] using h_bound

variable [DecidableEq X]

omit [Fintype X] in
/-- Let `l` and `k` be Harish-Chandra parameters, each stored as twice its value, and let the
weights of their lowest `K`-types vanish on `X` and be `μ` and `μ'` on the other coordinates; the
weights act as diagonal matrices. The columns `v₁, …, v_{d + 1}` of `positionVec` are the vectors
`[t ^ a q]`, `a ≤ d`, extended by `0` on `X`, and `i₀ = positionIsometry e e' μ μ'` is `1` on `ℂ^X`
and has multiples of the vectors `[q_j]` as its other columns. Then `μ i₀ = i₀ μ'` modulo the span
of the `v_a`, as `μ [q_j] = μ' j [q_j] + v₁`. -/
lemma exists_intDiagonal_mul_positionIsometry
    (h_zero : ∀ x : X, l.lowestKType (e (Sum.inl x)) = 0)
    (h_zero' : ∀ x : X, k.lowestKType (e' (Sum.inl x)) = 0)
    (hμ : ∀ i : Fin L, (l.lowestKType (e (Sum.inr i)) : ℝ) = μ i)
    (hμ' : ∀ j : Fin L', (k.lowestKType (e' (Sum.inr j)) : ℝ) = μ' j) :
    ∃ C : Matrix (Fin (d + 1)) m ℂ, intDiagonal l.lowestKType * positionIsometry e e' μ μ' =
      positionIsometry e e' μ μ' * intDiagonal k.lowestKType +
        positionVec e μ μ' d * C := by
  -- Only `v₁` is needed: its coefficient in the column of index `e' (Sum.inr j)` is the scale.
  let coeff (j : m) : ℂ :=
    Sum.elim 0 (fun j : Fin L' ↦ (isometryScale μ μ' j : ℂ)) (e'.symm j)
  let C : Matrix (Fin (d + 1)) m ℂ := of fun a j ↦ if a = 0 then coeff j else 0
  refine ⟨C, ?_⟩
  ext i j
  have h_mul : (positionVec e μ μ' d * C) i j = positionVec e μ μ' d i 0 * coeff j := by
    simp [C, mul_apply]
  rw [Matrix.add_apply, diagonal_mul, mul_diagonal, h_mul]
  obtain ⟨x' | j, rfl⟩ := e'.surjective j
  · obtain ⟨x | i, rfl⟩ := e.surjective i <;>
      simp [coeff, positionIsometry_apply_inl, h_zero, h_zero']
  · obtain ⟨x | i, rfl⟩ := e.surjective i
    · simp [positionIsometry_apply_inl_inr, positionVec_apply_inl]
    · have hi : (l.lowestKType (e (Sum.inr i)) : ℂ) = μ i := mod_cast hμ i
      have hj : (k.lowestKType (e' (Sum.inr j)) : ℂ) = μ' j := mod_cast hμ' j
      let w : ℝ := polyVec μ μ' (nodal (univ.erase j) μ') i
      let s : ℝ := isometryScale μ μ' j
      have h_shift : μ i * (s * w) = s * w * μ' j + polyVec μ μ' (nodal univ μ') i * s := by
        linear_combination s * mul_polyVec_erase (μ := μ) (μ' := μ') j i
      simpa [coeff, positionIsometry_apply_inr_inr, positionVec_apply_inr, hi, hj]
        using congrArg Complex.ofReal h_shift

/-- In a position `(v, i₀)` of `U(η)` in `U(ε)`, if `M i₀ = i₀ M'` modulo the span of the columns of
`v`, then `i₀† M i₀ = M'`. -/
lemma IsPosition.formAdjoint_mul_mul_eq {v : Matrix n (Fin (d + 1)) ℂ} {i₀ : Matrix n m ℂ}
    (h : IsPosition ε η d v i₀) {M : Matrix n n ℂ} {M' : Matrix m m ℂ}
    {C : Matrix (Fin (d + 1)) m ℂ} (hC : M * i₀ = i₀ * M' + v * C) :
    formAdjoint ε η i₀ * M * i₀ = M' :=
  calc
    formAdjoint ε η i₀ * M * i₀
        = signMatrix η * (i₀ᴴ * signMatrix ε * i₀) * M' +
          signMatrix η * (i₀ᴴ * signMatrix ε * v) * C := by
      simp only [formAdjoint, Matrix.mul_assoc, hC, Matrix.mul_add]
    _ = M' := by simp [h.isometry, h.orthogonal, signMatrix_mul_self]

/-- **The stationary position.** Let `l` be steep for `(X, L, B)` with `B ≥ 1`: on `X` the signs `ε`
are `+1` and the weight `μ` of its lowest `K`-type is `0`, and on the other `L` coordinates the
signs are `+, -, …` and `μ` decreases strictly in `[-3 B, -B]`. Let the weight `μ'` of the lowest
`K`-type of `k` vanish on `X`, where the signs `η` are `+1`, and increase strictly in `[0, B']` on
the other `L'` coordinates, where the signs are `+, -, …`. Let `B' ≥ 0` and `L = L' + 2 d + 1`. Then
there is a stationary position `(v, i₀)` with `j₀ = d + 1` vectors. Moreover `v_{j₀}` has the norm
`(-1) ^ L'`, and the entries of the `v_j`, of `i₀` and of `μ ^ a v₁` for `a ≤ 2 d` have modulus at
most `(3 B + B') ^ L`. -/
theorem IsSteep.exists_isStationary {l : HCParam ε} {k : HCParam η} {L L' d : ℕ}
    {e : X ⊕ Fin L ≃ n} {e' : X ⊕ Fin L' ≃ m} {B B' : ℝ} (hl : IsSteep l B e) (hB : 1 ≤ B)
    (hL : L = L' + 2 * d + 1) (hX_sign : ∀ x : X, η (e' (Sum.inl x)) = 1)
    (hX_zero : ∀ x : X, k.lowestKType (e' (Sum.inl x)) = 0)
    (h_alt : ∀ j : Fin L', η (e' (Sum.inr j)) = (-1) ^ j.val)
    (h_mono : StrictMono fun j : Fin L' ↦ k.lowestKType (e' (Sum.inr j))) (hB' : 0 ≤ B')
    (h_mem : ∀ j : Fin L', (k.lowestKType (e' (Sum.inr j)) : ℝ) ∈ Set.Icc 0 B') :
    ∃ (v : Matrix n (Fin (d + 1)) ℂ) (i₀ : Matrix n m ℂ),
      IsStationary l k e e' d v i₀ ∧
      (vᴴ * signMatrix ε * v) (Fin.last d) (Fin.last d) = (-1) ^ L' ∧
      (∀ (i : n) (a : Fin (d + 1)), ‖v i a‖ ≤ (3 * B + B') ^ L) ∧
      (∀ (i : n) (j : m), ‖i₀ i j‖ ≤ (3 * B + B') ^ L) ∧
      ∀ a : ℕ, a ≤ 2 * d → ∀ i : n,
        ‖(intDiagonal l.lowestKType ^ a *ᵥ v.col 0) i‖ ≤ (3 * B + B') ^ L := by
  let μ (i : Fin L) : ℝ := l.lowestKType (e (Sum.inr i))
  let μ' (j : Fin L') : ℝ := k.lowestKType (e' (Sum.inr j))
  have hμ (i : Fin L) : -3 * B ≤ μ i ∧ μ i ≤ -B := Set.mem_Icc.1 (hl.weight_mem i)
  have hμ' (j : Fin L') : 0 ≤ μ' j ∧ μ' j ≤ B' := Set.mem_Icc.1 (h_mem j)
  have h_opposite : AreOppositeNodes μ μ' :=
    { strictAnti := Int.cast_strictMono.comp_strictAnti hl.weight_strictAnti
      strictMono := Int.cast_strictMono.comp h_mono
      lt i j := by linarith [hμ i, hμ' j] }
  -- The roots of `p q` are distinct integers, so they differ by at least `1`.
  have h_one_le {a b : ℤ} (hab : a ≠ b) : 1 ≤ |(a : ℝ) - b| :=
    mod_cast Int.one_le_abs (sub_ne_zero.2 hab)
  have h_separated : AreSeparatedNodes μ μ' (3 * B + B') :=
    { one_le := by linarith
      pairwise_left i j hij := h_one_le (hl.weight_strictAnti.injective.ne hij)
      pairwise_right i j hij := h_one_le (h_mono.injective.ne hij)
      one_le_abs_sub i j := h_one_le (Int.cast_lt.1 (h_opposite.lt i j)).ne
      abs_sub_le i j := abs_le.2 ⟨by linarith [hμ i, hμ' j], by linarith [hμ i, hμ' j]⟩
      abs_le i := abs_le.2 ⟨by linarith [hμ i], by linarith [hμ i]⟩ }
  let v : Matrix n (Fin (d + 1)) ℂ := positionVec e μ μ' d
  let i₀ : Matrix n m ℂ := positionIsometry e e' μ μ'
  have h_position : IsPosition ε η d v i₀ := hl.isPosition h_opposite hL hX_sign h_alt
  obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin (d + 1)) m ℂ,
      intDiagonal l.lowestKType * i₀ = i₀ * intDiagonal k.lowestKType + v * C :=
    exists_intDiagonal_mul_positionIsometry hl.weight_eq_zero hX_zero (fun i ↦ rfl) fun j ↦ rfl
  have h_stationary : IsStationary l k e e' d v i₀ :=
    { h_position with
      shift := intDiagonal_mul_positionVec fun i ↦ rfl
      adjoint_weight_mul_eq := h_position.formAdjoint_mul_mul_eq hC
      apply_inl := positionIsometry_apply_inl }
  refine ⟨v, i₀, h_stationary, ?_, h_separated.norm_positionVec_le hL,
    h_separated.norm_positionIsometry_le hL,
    fun a ha ↦ h_separated.norm_pow_mulVec_positionVec_le hL (fun i ↦ rfl) ha⟩
  rw [hl.gram_positionVec h_opposite hL, Fin.val_last, ite_eq_left (two_mul d).symm]

end Matrices

end New.DiscreteSeries

end
