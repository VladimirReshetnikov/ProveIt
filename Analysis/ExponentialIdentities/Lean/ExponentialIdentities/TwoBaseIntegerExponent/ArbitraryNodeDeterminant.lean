import ExponentialIdentities.TwoBaseIntegerExponent
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Arbitrary-node interpolation determinants for two-base candidates

The repository's progression obstructions all use *equally spaced* nodes, because the forward
difference operator `Δ_[h]` is built from an arithmetic progression.  The same
integer-versus-small-real principle extends to *arbitrary* nodes through interpolation
determinants, and this file supplies the algebraic half of that extension.

For distinct nodes `x 0 < ⋯ < x r` and a function `f`, the classical identity

```
det ⎛ 1  x₀  ⋯  x₀ ^ (r-1)  f x₀ ⎞
    ⎜ 1  x₁  ⋯  x₁ ^ (r-1)  f x₁ ⎟ = V (x 0, …, x r) * f[x 0, …, x r],
    ⎝ ⋮  ⋮        ⋮          ⋮   ⎠
```

with `V (x 0, …, x r) = ∏_{i < j} (x j - x i)`, converts a determinant into a divided
difference; the generalized mean-value theorem then replaces the divided difference by
`f⁽ʳ⁾ ξ / r !`.  Taking `f t = t ^ θ` with `θ = log 3 / log 2` and `x i = m i` a strictly
increasing family of natural two-base candidates, every entry of the matrix is an integer:
the ordinary powers `m i ^ k` are integral by construction, and the last column `m i ^ θ` is
integral exactly because the `m i` are candidates.  A nonzero integer determinant has
absolute value at least one, and the analytic upper bound then forces the Vandermonde product
to be large --- a repulsion statement for candidate tuples with no assumed spacing structure.

This module deliberately contains **no analysis**.  It formalizes only the algebraic and
arithmetic plumbing:

* `nodeMatrix`, the arbitrary-node interpolation matrix, together with its entrywise
  description;
* `nodeIntMatrix`, an explicit integral model whose `Int.cast` image is `nodeMatrix`;
* `exists_int_det_nodeMatrix` and `one_le_abs_det_nodeMatrix`, the integrality of the
  determinant and the resulting lower bound `1 ≤ |det|`;
* `vandermondeProduct` with its positivity on strictly increasing nodes; and
* `abs_det_nodeMatrix_le_of_dividedDifference` and its corollaries, which take the
  determinant/divided-difference factorization and a bound on the divided difference *as
  hypotheses* and return the repulsion inequality.

The mean-value input `det = V * dd` with `|dd| ≤ B` is produced by a separate analytic
module; every statement here is phrased so that it plugs in unchanged.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

noncomputable section

/-! ## The interpolation matrix -/

/-- The interpolation matrix with ordinary-power columns `1, x, …, x ^ (r - 1)` and the
values of `f` in the final column.  Rows are indexed by the nodes `x i`. -/
def interpolationMatrix (r : ℕ) (x : Fin (r + 1) → ℝ) (f : ℝ → ℝ) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
  Matrix.of fun i j ↦ if j = Fin.last r then f (x i) else x i ^ (j : ℕ)

/-- Entrywise description of `interpolationMatrix`. -/
theorem interpolationMatrix_apply (r : ℕ) (x : Fin (r + 1) → ℝ) (f : ℝ → ℝ)
    (i j : Fin (r + 1)) :
    interpolationMatrix r x f i j =
      if j = Fin.last r then f (x i) else x i ^ (j : ℕ) := rfl

/-- The final column of `interpolationMatrix` records the values of `f`. -/
@[simp] theorem interpolationMatrix_apply_last (r : ℕ) (x : Fin (r + 1) → ℝ) (f : ℝ → ℝ)
    (i : Fin (r + 1)) :
    interpolationMatrix r x f i (Fin.last r) = f (x i) := by
  rw [interpolationMatrix_apply, if_pos rfl]

/-- Off the final column, `interpolationMatrix` carries ordinary powers. -/
theorem interpolationMatrix_apply_of_ne (r : ℕ) (x : Fin (r + 1) → ℝ) (f : ℝ → ℝ)
    {i j : Fin (r + 1)} (hj : j ≠ Fin.last r) :
    interpolationMatrix r x f i j = x i ^ (j : ℕ) := by
  rw [interpolationMatrix_apply, if_neg hj]

/-- The arbitrary-node matrix of the repulsion theorem: the first `r` columns carry the
ordinary powers `1, m, …, m ^ (r - 1)` and the last column carries `m ^ (log 3 / log 2)`. -/
def nodeMatrix (r : ℕ) (m : Fin (r + 1) → ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
  interpolationMatrix r (fun i ↦ (m i : ℝ)) fun t ↦ t ^ logThreeDivLogTwo

/-- Entrywise description of `nodeMatrix`. -/
theorem nodeMatrix_apply (r : ℕ) (m : Fin (r + 1) → ℕ) (i j : Fin (r + 1)) :
    nodeMatrix r m i j =
      if j = Fin.last r then (m i : ℝ) ^ logThreeDivLogTwo else (m i : ℝ) ^ (j : ℕ) := rfl

/-- The final column of `nodeMatrix` carries the candidate power `m i ^ (log 3 / log 2)`. -/
@[simp] theorem nodeMatrix_apply_last (r : ℕ) (m : Fin (r + 1) → ℕ) (i : Fin (r + 1)) :
    nodeMatrix r m i (Fin.last r) = (m i : ℝ) ^ logThreeDivLogTwo := by
  rw [nodeMatrix_apply, if_pos rfl]

/-- Off the final column the entries of `nodeMatrix` are ordinary natural powers. -/
theorem nodeMatrix_apply_of_ne (r : ℕ) (m : Fin (r + 1) → ℕ) {i j : Fin (r + 1)}
    (hj : j ≠ Fin.last r) :
    nodeMatrix r m i j = (m i : ℝ) ^ (j : ℕ) := by
  rw [nodeMatrix_apply, if_neg hj]

/-- The ordinary-power columns of `nodeMatrix`, indexed by `Fin r` through `Fin.castSucc`. -/
theorem nodeMatrix_apply_castSucc (r : ℕ) (m : Fin (r + 1) → ℕ) (i : Fin (r + 1))
    (j : Fin r) :
    nodeMatrix r m i j.castSucc = (m i : ℝ) ^ (j : ℕ) := by
  refine nodeMatrix_apply_of_ne r m ?_
  intro h
  have hval : (j : ℕ) = r := congrArg Fin.val h
  exact absurd hval j.isLt.ne

/-! ## The integral model -/

/-- The integral model of `nodeMatrix`: the ordinary-power columns are computed over `ℤ`
and the final column records integers `z i` witnessing integrality of `m i ^ θ`. -/
def nodeIntMatrix (r : ℕ) (m : Fin (r + 1) → ℕ) (z : Fin (r + 1) → ℤ) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℤ :=
  Matrix.of fun i j ↦ if j = Fin.last r then z i else (m i : ℤ) ^ (j : ℕ)

/-- Entrywise description of `nodeIntMatrix`. -/
theorem nodeIntMatrix_apply (r : ℕ) (m : Fin (r + 1) → ℕ) (z : Fin (r + 1) → ℤ)
    (i j : Fin (r + 1)) :
    nodeIntMatrix r m z i j =
      if j = Fin.last r then z i else (m i : ℤ) ^ (j : ℕ) := rfl

/-- The final column of the integral model records the chosen integer witnesses. -/
theorem nodeIntMatrix_apply_last (r : ℕ) (m : Fin (r + 1) → ℕ) (z : Fin (r + 1) → ℤ)
    (i : Fin (r + 1)) :
    nodeIntMatrix r m z i (Fin.last r) = z i := by
  rw [nodeIntMatrix_apply, if_pos rfl]

/-- Off the final column the integral model carries ordinary integer powers. -/
theorem nodeIntMatrix_apply_of_ne (r : ℕ) (m : Fin (r + 1) → ℕ) (z : Fin (r + 1) → ℤ)
    {i j : Fin (r + 1)} (hj : j ≠ Fin.last r) :
    nodeIntMatrix r m z i j = (m i : ℤ) ^ (j : ℕ) := by
  rw [nodeIntMatrix_apply, if_neg hj]

/-- Casting the integral model entrywise recovers the real node matrix. -/
theorem nodeIntMatrix_map (r : ℕ) (m : Fin (r + 1) → ℕ) (z : Fin (r + 1) → ℤ)
    (hz : ∀ i, (z i : ℝ) = (m i : ℝ) ^ logThreeDivLogTwo) :
    (nodeIntMatrix r m z).map (fun n : ℤ ↦ (n : ℝ)) = nodeMatrix r m := by
  ext i j
  simp only [Matrix.map_apply]
  by_cases hj : j = Fin.last r
  · subst hj
    rw [nodeIntMatrix_apply_last, nodeMatrix_apply_last]
    exact hz i
  · rw [nodeIntMatrix_apply_of_ne r m z hj, nodeMatrix_apply_of_ne r m hj]
    norm_cast

/-- **Every entry of the node matrix is an integer.**  The ordinary-power columns are
integral by construction; the final column is integral precisely because each `m i` is a
two-base natural candidate. -/
theorem nodeMatrix_entries_int (r : ℕ) (m : Fin (r + 1) → ℕ)
    (hcand : ∀ i, TwoBaseNaturalCandidate (m i)) :
    ∀ i j : Fin (r + 1), ∃ z : ℤ, (z : ℝ) = nodeMatrix r m i j := by
  intro i j
  by_cases hj : j = Fin.last r
  · subst hj
    have hmem : ∃ z : ℤ, (z : ℝ) = (m i : ℝ) ^ logThreeDivLogTwo := (hcand i).2
    obtain ⟨z, hz⟩ := hmem
    refine ⟨z, ?_⟩
    rw [nodeMatrix_apply_last]
    exact hz
  · refine ⟨(m i : ℤ) ^ (j : ℕ), ?_⟩
    rw [nodeMatrix_apply_of_ne r m hj]
    norm_cast

/-- The integral model exists as a genuine `Matrix _ _ ℤ` whose entrywise `Int.cast` image
is the node matrix. -/
theorem exists_intMatrix_map_eq_nodeMatrix (r : ℕ) (m : Fin (r + 1) → ℕ)
    (hcand : ∀ i, TwoBaseNaturalCandidate (m i)) :
    ∃ Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℤ,
      Z.map (fun n : ℤ ↦ (n : ℝ)) = nodeMatrix r m := by
  have hz : ∀ i : Fin (r + 1), ∃ z : ℤ, (z : ℝ) = (m i : ℝ) ^ logThreeDivLogTwo :=
    fun i ↦ (hcand i).2
  choose z hzeq using hz
  exact ⟨nodeIntMatrix r m z, nodeIntMatrix_map r m z hzeq⟩

/-- **The node determinant is the cast of an integer.** -/
theorem exists_int_det_nodeMatrix (r : ℕ) (m : Fin (r + 1) → ℕ)
    (hcand : ∀ i, TwoBaseNaturalCandidate (m i)) :
    ∃ D : ℤ, (D : ℝ) = (nodeMatrix r m).det := by
  obtain ⟨Z, hZ⟩ := exists_intMatrix_map_eq_nodeMatrix r m hcand
  refine ⟨Z.det, ?_⟩
  rw [Int.cast_det, hZ]

/-- Restatement of `exists_int_det_nodeMatrix` as a range membership, matching the
integrality convention used throughout the corpus. -/
theorem det_nodeMatrix_mem_intCast (r : ℕ) (m : Fin (r + 1) → ℕ)
    (hcand : ∀ i, TwoBaseNaturalCandidate (m i)) :
    (nodeMatrix r m).det ∈ Set.range ((↑) : ℤ → ℝ) := by
  obtain ⟨D, hD⟩ := exists_int_det_nodeMatrix r m hcand
  exact ⟨D, hD⟩

/-- **A nonzero node determinant has absolute value at least one.**  This is the arithmetic
half of the repulsion argument. -/
theorem one_le_abs_det_nodeMatrix (r : ℕ) (m : Fin (r + 1) → ℕ)
    (hcand : ∀ i, TwoBaseNaturalCandidate (m i))
    (hne : (nodeMatrix r m).det ≠ 0) :
    1 ≤ |(nodeMatrix r m).det| :=
  IntegerExponent.one_le_abs_det_of_integer_entries (nodeMatrix r m)
    (nodeMatrix_entries_int r m hcand) hne

/-! ## The Vandermonde product -/

/-- The Vandermonde product `∏_{i < j} (m j - m i)` of the nodes. -/
def vandermondeProduct (r : ℕ) (m : Fin (r + 1) → ℕ) : ℝ :=
  ∏ i : Fin (r + 1), ∏ j ∈ Finset.Ioi i, ((m j : ℝ) - (m i : ℝ))

/-- The Vandermonde product is the determinant of the ordinary Vandermonde matrix on the
same nodes. -/
theorem vandermondeProduct_eq_det_vandermonde (r : ℕ) (m : Fin (r + 1) → ℕ) :
    vandermondeProduct r m =
      (Matrix.vandermonde fun i : Fin (r + 1) ↦ (m i : ℝ)).det :=
  (Matrix.det_vandermonde _).symm

/-- **Positivity of the Vandermonde product for strictly increasing nodes.** -/
theorem vandermondeProduct_pos (r : ℕ) (m : Fin (r + 1) → ℕ) (hm : StrictMono m) :
    0 < vandermondeProduct r m := by
  have h : ∀ i : Fin (r + 1), ∀ j ∈ Finset.Ioi i, (0 : ℝ) < (m j : ℝ) - (m i : ℝ) := by
    intro i j hj
    have hlt : (m i : ℝ) < (m j : ℝ) := by
      exact_mod_cast hm (Finset.mem_Ioi.mp hj)
    linarith
  show 0 < ∏ i : Fin (r + 1), ∏ j ∈ Finset.Ioi i, ((m j : ℝ) - (m i : ℝ))
  exact Finset.prod_pos fun i _ ↦ Finset.prod_pos (h i)

/-- The Vandermonde product of strictly increasing nodes is nonzero. -/
theorem vandermondeProduct_ne_zero (r : ℕ) (m : Fin (r + 1) → ℕ) (hm : StrictMono m) :
    vandermondeProduct r m ≠ 0 :=
  (vandermondeProduct_pos r m hm).ne'

/-! ## The divided-difference bridge

The analytic module supplies a factorization `det = V * dd` together with a bound
`|dd| ≤ B`.  The statements below consume exactly that data as hypotheses; nothing analytic
is proved here. -/

/-- **The divided-difference bridge.**  Given a factorization of the node determinant into a
Vandermonde factor `V` and a divided-difference factor `dd`, and a bound on the latter, the
determinant obeys the corresponding product bound. -/
theorem abs_det_nodeMatrix_le_of_dividedDifference (r : ℕ) (m : Fin (r + 1) → ℕ)
    {V dd B : ℝ} (hdd : (nodeMatrix r m).det = V * dd) (hdd_bound : |dd| ≤ B) :
    |(nodeMatrix r m).det| ≤ |V| * B := by
  rw [hdd, abs_mul]
  exact mul_le_mul_of_nonneg_left hdd_bound (abs_nonneg V)

private theorem inv_le_of_one_le_mul {V B : ℝ} (hB : 0 < B) (h : 1 ≤ V * B) : B⁻¹ ≤ V := by
  have hBne : B ≠ 0 := hB.ne'
  have hinv : (0 : ℝ) < B⁻¹ := inv_pos.mpr hB
  have hcalc : B⁻¹ * (V * B) = V := by
    rw [mul_comm V B, ← mul_assoc, inv_mul_cancel₀ hBne, one_mul]
  calc B⁻¹ = B⁻¹ * 1 := (mul_one _).symm
    _ ≤ B⁻¹ * (V * B) := mul_le_mul_of_nonneg_left h hinv.le
    _ = V := hcalc

/-- **Algebraic core of the arbitrary-node repulsion theorem.**  If the nodes are strictly
increasing two-base candidates, the node determinant is nonzero, and it factors as `V * dd`
with `V` the Vandermonde product and `|dd| ≤ B`, then `1 ≤ V * B`. -/
theorem one_le_vandermondeProduct_mul_of_dividedDifference (r : ℕ) (m : Fin (r + 1) → ℕ)
    (hstrict : StrictMono m) (hcand : ∀ i, TwoBaseNaturalCandidate (m i)) {dd B : ℝ}
    (hdet : (nodeMatrix r m).det = vandermondeProduct r m * dd)
    (hdd_bound : |dd| ≤ B) (hne : (nodeMatrix r m).det ≠ 0) :
    1 ≤ vandermondeProduct r m * B := by
  have hV : 0 < vandermondeProduct r m := vandermondeProduct_pos r m hstrict
  have h1 : (1 : ℝ) ≤ |(nodeMatrix r m).det| := one_le_abs_det_nodeMatrix r m hcand hne
  have h2 : |(nodeMatrix r m).det| ≤ |vandermondeProduct r m| * B :=
    abs_det_nodeMatrix_le_of_dividedDifference r m hdet hdd_bound
  rw [abs_of_pos hV] at h2
  linarith

/-- **Arbitrary-node repulsion, packaged form.**  Under the same hypotheses the Vandermonde
product is at least `B⁻¹`.  With the analytic value
`B = |fallingRpowCoeff θ r| / r ! * m 0 ^ (θ - r)` this is exactly the bound of the report's
arbitrary-node theorem. -/
theorem inv_le_vandermondeProduct_of_dividedDifference (r : ℕ) (m : Fin (r + 1) → ℕ)
    (hstrict : StrictMono m) (hcand : ∀ i, TwoBaseNaturalCandidate (m i)) {dd B : ℝ}
    (hB : 0 < B) (hdet : (nodeMatrix r m).det = vandermondeProduct r m * dd)
    (hdd_bound : |dd| ≤ B) (hne : (nodeMatrix r m).det ≠ 0) :
    B⁻¹ ≤ vandermondeProduct r m :=
  inv_le_of_one_le_mul hB
    (one_le_vandermondeProduct_mul_of_dividedDifference r m hstrict hcand hdet hdd_bound hne)

end

end LeanProofs.TwoBaseIntegerExponent
