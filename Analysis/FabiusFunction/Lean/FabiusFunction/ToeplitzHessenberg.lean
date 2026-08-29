import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Toeplitz–Hessenberg determinants and the convolution system

A *lower Toeplitz–Hessenberg matrix* is a square matrix whose entries depend
only on `i - j` on and below the diagonal, whose first superdiagonal is an
arbitrary sequence, and which vanishes above that superdiagonal:

```
H i j = if j = i + 1 then d i else if j ≤ i then a (i - j + 1) else 0
```

Its determinant is classically computed by expanding along the last row, which
produces a linear recurrence.  The route taken here avoids every determinant
expansion.  The same data `(d, a)` also assemble a *lower triangular* matrix

```
T m j = if j = m then d m else if j < m then a (m - j) else 0
```

whose determinant is visibly `∏ d`, and a single cyclic rotation of the columns
carries `H`, with its first column negated, onto `T` with its last column
replaced by `-(a 1, …, a n)`.  Cramer's rule therefore reads off `det H` from
*any* solution of the convolution system `T *ᵥ x = -(a 1, …, a n)`, that is,
from any sequence satisfying

`d m · y m + ∑_{j < m} a (m - j) · y j = -a (m + 1)`.

Everything is over an arbitrary commutative ring, with arbitrary `d` and `a`;
no invertibility and no positivity is assumed anywhere.

## Main results

* `Matrix.cramer_mulVec` — Cramer's rule for a vector already known to be a
  solution: `A.cramer (A *ᵥ x) = A.det • x`, over any commutative ring.
* `Fabius.det_triBand` — `det (triBand n d a) = ∏ i ∈ range n, d i`.
* `Fabius.det_hessBand` — **the determinant formula**
  `det (hessBand (n+1) d a) = (-1)^(n+1) · (∏ i ∈ range (n+1), d i) · x (last n)`
  for every solution `x` of the convolution system.
* `Fabius.det_hessBand_of_recurrence` — the same conclusion phrased directly in
  terms of the scalar recurrence, with no matrix hypothesis; this is the form
  used by callers.
-/

set_option autoImplicit false

open Finset

namespace Matrix

/-- **Cramer's rule for a known solution**, over any commutative ring: the
Cramer map applied to `A *ᵥ x` returns `det A • x`.  (Replacing a column of `A`
by a linear combination of its columns keeps only the diagonal term of the
expanded determinant.) -/
theorem cramer_mulVec {n : Type*} [DecidableEq n] [Fintype n]
    {R : Type*} [CommRing R] (A : Matrix n n R) (x : n → R) :
    A.cramer (A.mulVec x) = A.det • x := by
  have hexpand : A.mulVec x = ∑ j, x j • (fun i => A i j) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hexpand, map_sum]
  funext i
  have hterm : ∀ j, A.cramer (fun k => A k j) =
      (Pi.single j A.det : n → R) :=
    fun j => Matrix.cramer_row_self A _ j fun k => rfl
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul,
    hterm, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl]
    ring
  · intro j _ hj
    rw [if_neg fun h => hj h.symm, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

end Matrix

namespace Fabius

open Matrix

variable {R : Type*} [CommRing R]

/-- The lower triangular matrix of the convolution system: diagonal `d`, and
the Toeplitz band `a (m - j)` strictly below it. -/
def triBand (n : ℕ) (d a : ℕ → R) : Matrix (Fin n) (Fin n) R :=
  fun m j =>
    if (j : ℕ) = (m : ℕ) then d (m : ℕ)
    else if (j : ℕ) < (m : ℕ) then a ((m : ℕ) - (j : ℕ)) else 0

/-- The lower Toeplitz–Hessenberg matrix: Toeplitz band `a (i - j + 1)` on and
below the diagonal, superdiagonal `d`, zero above. -/
def hessBand (n : ℕ) (d a : ℕ → R) : Matrix (Fin n) (Fin n) R :=
  fun i j =>
    if (j : ℕ) = (i : ℕ) + 1 then d (i : ℕ)
    else if (j : ℕ) ≤ (i : ℕ) then a ((i : ℕ) - (j : ℕ) + 1) else 0

/-- The diagonal entries of the triangular band matrix are the diagonal sequence `d`. -/
@[simp]
theorem triBand_apply_diag (n : ℕ) (d a : ℕ → R) (m : Fin n) :
    triBand n d a m m = d (m : ℕ) := by
  simp [triBand]

/-- The first column of the lower Hessenberg band records the shifted Toeplitz sequence `a`. -/
@[simp]
theorem hessBand_apply_zero (n : ℕ) (d a : ℕ → R) (i : Fin (n + 1)) :
    hessBand (n + 1) d a i 0 = a ((i : ℕ) + 1) := by
  simp only [hessBand]
  rw [show ((0 : Fin (n + 1)) : ℕ) = 0 from rfl, if_neg (by omega),
    if_pos (by omega), Nat.sub_zero]

/-- The convolution system in scalar form: applied to the restriction of a
sequence `y : ℕ → R`, the matrix `T` produces, in row `m`, the weighted sum
`d m · y m + ∑_{j < m} a (m - j) · y j`. -/
theorem triBand_mulVec_apply (n : ℕ) (d a y : ℕ → R) (m : Fin n) :
    (triBand n d a).mulVec (fun j : Fin n => y (j : ℕ)) m =
      d (m : ℕ) * y (m : ℕ) + ∑ j ∈ range (m : ℕ), a ((m : ℕ) - j) * y j := by
  simp only [Matrix.mulVec, dotProduct]
  have hfin : ∑ j : Fin n, triBand n d a m j * y (j : ℕ) =
      ∑ j ∈ range n,
        (if j = (m : ℕ) then d (m : ℕ)
          else if j < (m : ℕ) then a ((m : ℕ) - j) else 0) * y j := by
    rw [← Fin.sum_univ_eq_sum_range (fun j =>
      (if j = (m : ℕ) then d (m : ℕ)
        else if j < (m : ℕ) then a ((m : ℕ) - j) else 0) * y j) n]
    rfl
  rw [hfin]
  have hsub : ∑ j ∈ range ((m : ℕ) + 1),
      (if j = (m : ℕ) then d (m : ℕ)
        else if j < (m : ℕ) then a ((m : ℕ) - j) else 0) * y j =
      ∑ j ∈ range n,
        (if j = (m : ℕ) then d (m : ℕ)
          else if j < (m : ℕ) then a ((m : ℕ) - j) else 0) * y j := by
    refine Finset.sum_subset ?_ ?_
    · intro j hj
      have := Finset.mem_range.mp hj
      have hm := m.isLt
      exact Finset.mem_range.mpr (by omega)
    · intro j _ hj
      have hgt : ¬ j < (m : ℕ) + 1 := fun hc => hj (Finset.mem_range.mpr hc)
      rw [if_neg (by omega), if_neg (by omega), zero_mul]
  rw [← hsub, Finset.sum_range_succ, if_pos rfl, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have := Finset.mem_range.mp hj
  rw [if_neg (by omega), if_pos (by omega)]

/-- The determinant of the triangular system matrix is the product of its
diagonal. -/
theorem det_triBand (n : ℕ) (d a : ℕ → R) :
    (triBand n d a).det = ∏ i ∈ range n, d i := by
  have htri : (triBand n d a).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hlt : i < j := hij
    have : (i : ℕ) < (j : ℕ) := hlt
    simp only [triBand]
    rw [if_neg (by omega), if_neg (by omega)]
  rw [Matrix.det_of_lowerTriangular _ htri,
    Finset.prod_congr rfl fun i _ => triBand_apply_diag n d a i]
  exact Fin.prod_univ_eq_prod_range (fun i => d i) n

/-- **The Toeplitz–Hessenberg determinant formula.**  If `x` solves the
convolution system `T *ᵥ x = -(a 1, …, a (n+1))`, then

`det (hessBand (n+1) d a) = (-1)^(n+1) · (∏ i ∈ range (n+1), d i) · x (last n)`.

The proof is a single cyclic column rotation followed by Cramer's rule; no
determinant is ever expanded. -/
theorem det_hessBand (n : ℕ) (d a : ℕ → R) (x : Fin (n + 1) → R)
    (hx : (triBand (n + 1) d a).mulVec x =
      fun m : Fin (n + 1) => -a ((m : ℕ) + 1)) :
    (hessBand (n + 1) d a).det =
      (-1) ^ (n + 1) * (∏ i ∈ range (n + 1), d i) * x (Fin.last n) := by
  -- Cramer at the last column of the triangular system
  have hcram : ((triBand (n + 1) d a).updateCol (Fin.last n)
        (fun m : Fin (n + 1) => -a ((m : ℕ) + 1))).det =
      (∏ i ∈ range (n + 1), d i) * x (Fin.last n) := by
    have h := congrFun (Matrix.cramer_mulVec (triBand (n + 1) d a) x)
      (Fin.last n)
    rw [hx, Matrix.cramer_apply, det_triBand] at h
    rw [h]
    simp only [Pi.smul_apply, smul_eq_mul]
  -- the column rotation: `H` with its first column negated, read through
  -- `finRotate`, is `T` with its last column replaced by `-(a 1, …, a (n+1))`
  have hrot : ((hessBand (n + 1) d a).updateCol 0
        (fun i => -hessBand (n + 1) d a i 0)).submatrix id
        (finRotate (n + 1)) =
      (triBand (n + 1) d a).updateCol (Fin.last n)
        (fun m : Fin (n + 1) => -a ((m : ℕ) + 1)) := by
    funext i j
    simp only [Matrix.submatrix_apply, id_eq, finRotate_apply]
    by_cases hj : j = Fin.last n
    · subst hj
      rw [Fin.last_add_one, Matrix.updateCol_apply, if_pos rfl,
        Matrix.updateCol_apply, if_pos rfl, hessBand_apply_zero]
    · have hjlt : (j : ℕ) < n := by
        have := j.isLt
        rcases Nat.lt_or_ge (j : ℕ) n with h | h
        · exact h
        · exact absurd (Fin.ext (by rw [Fin.val_last]; omega) :
            j = Fin.last n) hj
      have hval : ((j + 1 : Fin (n + 1)) : ℕ) = (j : ℕ) + 1 :=
        Fin.val_add_one_of_lt' (by omega)
      have hne0 : (j + 1 : Fin (n + 1)) ≠ 0 := by
        intro h
        have := congrArg (fun t : Fin (n + 1) => (t : ℕ)) h
        simp only [hval, Fin.val_zero] at this
        omega
      rw [Matrix.updateCol_apply, if_neg hne0, Matrix.updateCol_apply,
        if_neg hj]
      simp only [hessBand, triBand, hval]
      split_ifs with h1 h2 h3 h4 h5 <;> first
        | rfl
        | omega
        | (congr 1; omega)
  -- determinant bookkeeping: negate one column, then permute the columns
  have hupd : (hessBand (n + 1) d a).updateCol 0
      (fun i => hessBand (n + 1) d a i 0) = hessBand (n + 1) d a := by
    funext i j
    rw [Matrix.updateCol_apply]
    split_ifs with h
    · subst h; rfl
    · rfl
  have hdetH' : ((hessBand (n + 1) d a).updateCol 0
        (fun i => -hessBand (n + 1) d a i 0)).det =
      -(hessBand (n + 1) d a).det := by
    have hsmul : (fun i => -hessBand (n + 1) d a i 0) =
        (-1 : R) • (fun i => hessBand (n + 1) d a i 0) := by
      funext i
      simp
    rw [hsmul, Matrix.det_updateCol_smul, hupd]
    ring
  have hperm := Matrix.det_permute' (finRotate (n + 1))
    ((hessBand (n + 1) d a).updateCol 0
      (fun i => -hessBand (n + 1) d a i 0))
  rw [hrot, hcram, hdetH', sign_finRotate] at hperm
  simp only [Nat.add_sub_cancel, Units.val_pow_eq_pow_val, Units.val_neg,
    Units.val_one, Int.cast_pow, Int.cast_neg, Int.cast_one] at hperm
  have hsq : ((-1 : R) ^ n) * ((-1 : R) ^ n) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have hkey : (-1 : R) ^ n *
      ((∏ i ∈ range (n + 1), d i) * x (Fin.last n)) =
      -(hessBand (n + 1) d a).det := by
    rw [hperm, ← mul_assoc, hsq, one_mul]
  have hdetH : (hessBand (n + 1) d a).det =
      -((-1 : R) ^ n * ((∏ i ∈ range (n + 1), d i) * x (Fin.last n))) := by
    rw [hkey, neg_neg]
  rw [hdetH, pow_succ]
  ring

/-- **The Toeplitz–Hessenberg determinant formula, scalar form.**  If a
sequence `y : ℕ → R` satisfies the convolution recurrence

`d m · y m + ∑_{j < m} a (m - j) · y j = -a (m + 1)`  for every `m ≤ n`,

then `det (hessBand (n+1) d a) = (-1)^(n+1) · (∏ i ∈ range (n+1), d i) · y n`.

No hypothesis is placed on `d`; in particular the recurrence need not
determine `y`, and any solution gives the same determinant. -/
theorem det_hessBand_of_recurrence (n : ℕ) (d a y : ℕ → R)
    (hy : ∀ m ≤ n, d m * y m + ∑ j ∈ range m, a (m - j) * y j = -a (m + 1)) :
    (hessBand (n + 1) d a).det =
      (-1) ^ (n + 1) * (∏ i ∈ range (n + 1), d i) * y n := by
  have hx : (triBand (n + 1) d a).mulVec (fun j : Fin (n + 1) => y (j : ℕ)) =
      fun m : Fin (n + 1) => -a ((m : ℕ) + 1) := by
    funext m
    rw [triBand_mulVec_apply]
    exact hy (m : ℕ) (by omega)
  simpa using det_hessBand n d a (fun j : Fin (n + 1) => y (j : ℕ)) hx

end Fabius
