import FabiusFunction.MomentHankelMatrix
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The determinant construction of the up-measure's orthogonal polynomials

Stage two of the integration volume's *orthogonal-polynomial layer*
obligation: the orthogonal polynomials themselves, by the classical
bordered-Hankel determinant construction.

* `borderedHankel F n x` — the `(n+1) × (n+1)` matrix whose first `n`
  rows are the moment rows `(m_{i+j})_j` and whose last row is the
  monomial row `(1, x, …, xⁿ)`;
* `hankelOrthoValue F n x` — its determinant, the classical
  determinant representation `h_n·P_n(x)` of the orthogonal
  polynomial;
* `integral_hankelOrthoValue_mul_pow` — **the orthogonality
  relations**: `∫ P_n(x)·x^{j} dμ_up = 0` for every `j < n`.  The
  proof is the classical one made formal: expanding along the last
  row turns the integral into the determinant of the matrix whose
  last row is the `j`-shifted moment row, which duplicates row `j`;
* `hankelOrthoPolynomial` — the construction as a genuine
  `Polynomial ℝ`, with exact degree `n`, leading coefficient `h_n`,
  and the monic normalization `upOrthoPolynomial`;
* `integral_hankelOrthoValue_mul_pow_self` — the `j = n` companion:
  the integral against the leading monomial is the *next* Hankel
  determinant `h_{n+1}`, because the `n`-shifted moment row completes
  the `(n+1)`-th Hankel block;
* `integral_upOrthoPolynomial_sq` — **the norm identity**
  `∫ P_n(x)² dμ_up = h_{n+1}/h_n`, combining the previous two through
  orthogonality against all lower-degree polynomials
  (`integral_hankelOrthoValue_mul_eval`).
-/

set_option autoImplicit false

open MeasureTheory Matrix

namespace Fabius

/-- The bordered Hankel matrix: moment rows on top, the monomial row
at the bottom. -/
noncomputable def borderedHankel (F : BoundedFabius) (n : ℕ) (x : ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) < n then upMoment F ((i : ℕ) + j) else x ^ (j : ℕ)

/-- The determinant orthogonal-polynomial values `h_n·P_n(x)`. -/
noncomputable def hankelOrthoValue (F : BoundedFabius) (n : ℕ)
    (x : ℝ) : ℝ :=
  (borderedHankel F n x).det

/-- The comparison matrix whose last row is the `j'`-shifted moment
row. -/
noncomputable def momentBordered (F : BoundedFabius) (n j' : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) < n then upMoment F ((i : ℕ) + j)
    else upMoment F ((j : ℕ) + j')

/-- For `j' < n` the comparison matrix has a duplicated row, so its
determinant vanishes. -/
theorem det_momentBordered_eq_zero (F : BoundedFabius) (n : ℕ)
    {j' : ℕ} (hj : j' < n) :
    (momentBordered F n j').det = 0 := by
  refine Matrix.det_zero_of_row_eq
    (i := (⟨j', by omega⟩ : Fin (n + 1))) (j := Fin.last n) ?_ ?_
  · intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_last] at hval
    omega
  · funext col
    show (if j' < n then upMoment F (j' + col) else _) =
      (if (Fin.last n : ℕ) < n then upMoment F ((Fin.last n : ℕ) + col)
        else upMoment F ((col : ℕ) + j'))
    rw [if_pos hj, if_neg (by simp [Fin.val_last]), Nat.add_comm]

/-- The last-row minors of the bordered matrix are `x`-free: they
agree with the minors of the comparison matrix. -/
theorem submatrix_borderedHankel_eq (F : BoundedFabius) (n : ℕ)
    (x : ℝ) (j' : ℕ) (j : Fin (n + 1)) :
    (borderedHankel F n x).submatrix (Fin.last n).succAbove
        j.succAbove =
      (momentBordered F n j').submatrix (Fin.last n).succAbove
        j.succAbove := by
  ext i' col'
  simp only [Matrix.submatrix_apply, Fin.succAbove_last]
  have hlt : ((Fin.castSucc i' : Fin (n + 1)) : ℕ) < n := by
    simpa using i'.isLt
  show (if ((Fin.castSucc i' : Fin (n + 1)) : ℕ) < n then _ else _) =
    (if ((Fin.castSucc i' : Fin (n + 1)) : ℕ) < n then _ else _)
  rw [if_pos hlt, if_pos hlt]

/-- Integrating the determinant polynomial against a monomial
produces a bordered *moment* determinant: the monomial row of the
bordered matrix is replaced by the `j'`-shifted moment row. -/
theorem integral_hankelOrthoValue_mul_pow_eq_det (F : BoundedFabius)
    (hF : IsFabius F) (n j' : ℕ) :
    ∫ x, hankelOrthoValue F n x * x ^ j' ∂(rvachevMeasure F) =
      (momentBordered F n j').det := by
  have hlastrow : ∀ (x : ℝ) (j : Fin (n + 1)),
      borderedHankel F n x (Fin.last n) j = x ^ (j : ℕ) := by
    intro x j
    show (if (Fin.last n : ℕ) < n then upMoment F _ else x ^ (j : ℕ)) =
      x ^ (j : ℕ)
    rw [if_neg (by simp [Fin.val_last])]
  have hexpand : (fun x : ℝ => hankelOrthoValue F n x * x ^ j') =
      fun x : ℝ => ∑ j : Fin (n + 1),
        ((-1 : ℝ) ^ ((Fin.last n : ℕ) + (j : ℕ)) *
          ((momentBordered F n j').submatrix (Fin.last n).succAbove
            j.succAbove).det) * x ^ ((j : ℕ) + j') := by
    funext x
    rw [hankelOrthoValue, Matrix.det_succ_row _ (Fin.last n),
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hlastrow x j, submatrix_borderedHankel_eq F n x j' j, pow_add]
    ring
  rw [hexpand, integral_finsetSum _ fun j _ =>
    (integrable_pow_rvachevMeasure F hF _).const_mul _]
  have hsum : ∀ j : Fin (n + 1),
      ∫ x, ((-1 : ℝ) ^ ((Fin.last n : ℕ) + (j : ℕ)) *
        ((momentBordered F n j').submatrix (Fin.last n).succAbove
          j.succAbove).det) * x ^ ((j : ℕ) + j')
        ∂(rvachevMeasure F) =
      ((-1 : ℝ) ^ ((Fin.last n : ℕ) + (j : ℕ)) *
        ((momentBordered F n j').submatrix (Fin.last n).succAbove
          j.succAbove).det) * upMoment F ((j : ℕ) + j') := by
    intro j
    rw [MeasureTheory.integral_const_mul]
    rfl
  rw [Finset.sum_congr rfl fun j _ => hsum j]
  have hdet := Matrix.det_succ_row (momentBordered F n j') (Fin.last n)
  have hlast : ∀ j : Fin (n + 1),
      momentBordered F n j' (Fin.last n) j =
        upMoment F ((j : ℕ) + j') := by
    intro j
    show (if (Fin.last n : ℕ) < n then upMoment F _
      else upMoment F ((j : ℕ) + j')) = upMoment F ((j : ℕ) + j')
    rw [if_neg (by simp [Fin.val_last])]
  calc ∑ j : Fin (n + 1),
        ((-1 : ℝ) ^ ((Fin.last n : ℕ) + (j : ℕ)) *
          ((momentBordered F n j').submatrix (Fin.last n).succAbove
            j.succAbove).det) * upMoment F ((j : ℕ) + j')
      = (momentBordered F n j').det := by
        rw [hdet]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hlast j]
        ring

/-- **The orthogonality relations**: the determinant polynomial is
orthogonal to every lower monomial, `∫ P_n(x)·x^{j'} dμ_up = 0` for
`j' < n`. -/
theorem integral_hankelOrthoValue_mul_pow (F : BoundedFabius)
    (hF : IsFabius F) (n : ℕ) {j' : ℕ} (hj : j' < n) :
    ∫ x, hankelOrthoValue F n x * x ^ j' ∂(rvachevMeasure F) = 0 := by
  rw [integral_hankelOrthoValue_mul_pow_eq_det F hF n j',
    det_momentBordered_eq_zero F n hj]

/-- At `j' = n` the comparison matrix completes the moment rows to the
full `(n+1)`-th Hankel block. -/
theorem momentBordered_self (F : BoundedFabius) (n : ℕ) :
    momentBordered F n n = momentHankel F (n + 1) := by
  ext i j
  have hi := i.isLt
  show (if (i : ℕ) < n then upMoment F ((i : ℕ) + j)
    else upMoment F ((j : ℕ) + n)) = upMoment F ((i : ℕ) + j)
  by_cases h : (i : ℕ) < n
  · rw [if_pos h]
  · rw [if_neg h]
    have hin : (i : ℕ) = n := by omega
    rw [hin, Nat.add_comm]

/-- **The norm-producing moment**: integrating the determinant
polynomial against its own leading monomial produces the *next* Hankel
determinant, `∫ (h_nP_n)(x)·x^{n} dμ_up = h_{n+1}`. -/
theorem integral_hankelOrthoValue_mul_pow_self (F : BoundedFabius)
    (hF : IsFabius F) (n : ℕ) :
    ∫ x, hankelOrthoValue F n x * x ^ n ∂(rvachevMeasure F) =
      hankelDet F (n + 1) := by
  rw [integral_hankelOrthoValue_mul_pow_eq_det F hF n n,
    momentBordered_self]
  rfl

section PolynomialForm

/-- The `n`-th orthogonal polynomial `h_n·P_n` as a `Polynomial ℝ`:
the cofactor expansion of the bordered determinant along its monomial
row. -/
noncomputable def hankelOrthoPolynomial (F : BoundedFabius) (n : ℕ) :
    Polynomial ℝ :=
  ∑ j : Fin (n + 1),
    Polynomial.C ((-1 : ℝ) ^ ((Fin.last n : ℕ) + (j : ℕ)) *
      ((momentBordered F n 0).submatrix (Fin.last n).succAbove
        j.succAbove).det) * Polynomial.X ^ (j : ℕ)

/-- The polynomial evaluates to the bordered determinant. -/
theorem hankelOrthoPolynomial_eval (F : BoundedFabius) (n : ℕ)
    (x : ℝ) :
    (hankelOrthoPolynomial F n).eval x = hankelOrthoValue F n x := by
  rw [hankelOrthoPolynomial, hankelOrthoValue,
    Matrix.det_succ_row _ (Fin.last n)]
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hlastrow : borderedHankel F n x (Fin.last n) j = x ^ (j : ℕ) := by
    show (if (Fin.last n : ℕ) < n then upMoment F _ else x ^ (j : ℕ)) =
      x ^ (j : ℕ)
    rw [if_neg (by simp [Fin.val_last])]
  rw [hlastrow, ← submatrix_borderedHankel_eq F n x 0 j]
  simp only [Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  ring

/-- Coefficient extraction: the `j₀`-th coefficient is the signed
minor. -/
theorem hankelOrthoPolynomial_coeff (F : BoundedFabius) (n : ℕ)
    (j₀ : Fin (n + 1)) :
    (hankelOrthoPolynomial F n).coeff (j₀ : ℕ) =
      (-1 : ℝ) ^ ((Fin.last n : ℕ) + (j₀ : ℕ)) *
        ((momentBordered F n 0).submatrix (Fin.last n).succAbove
          j₀.succAbove).det := by
  rw [hankelOrthoPolynomial, Polynomial.finsetSum_coeff]
  have hterm : ∀ j : Fin (n + 1),
      (Polynomial.C ((-1 : ℝ) ^ ((Fin.last n : ℕ) + (j : ℕ)) *
        ((momentBordered F n 0).submatrix (Fin.last n).succAbove
          j.succAbove).det) * Polynomial.X ^ (j : ℕ)).coeff (j₀ : ℕ) =
      if j₀ = j then
        (-1 : ℝ) ^ ((Fin.last n : ℕ) + (j : ℕ)) *
          ((momentBordered F n 0).submatrix (Fin.last n).succAbove
            j.succAbove).det
      else 0 := by
    intro j
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases h : j₀ = j
    · subst h
      simp
    · rw [if_neg (fun hval => h (Fin.val_injective hval)),
        mul_zero, if_neg h]
  simp_rw [hterm]
  rw [Finset.sum_ite_eq Finset.univ j₀ _, if_pos (Finset.mem_univ _)]

/-- The last minor is the plain Hankel block, so the top coefficient
is the Hankel determinant `h_n`. -/
theorem hankelOrthoPolynomial_coeff_top (F : BoundedFabius) (n : ℕ) :
    (hankelOrthoPolynomial F n).coeff n = hankelDet F n := by
  have h := hankelOrthoPolynomial_coeff F n (Fin.last n)
  rw [Fin.val_last] at h
  have hsub : (momentBordered F n 0).submatrix (Fin.last n).succAbove
      (Fin.last n).succAbove = momentHankel F n := by
    ext i' col'
    simp only [Matrix.submatrix_apply, Fin.succAbove_last]
    show (if ((Fin.castSucc i' : Fin (n + 1)) : ℕ) < n then
      upMoment F (((Fin.castSucc i' : Fin (n + 1)) : ℕ) +
        ((Fin.castSucc col' : Fin (n + 1)) : ℕ))
      else upMoment F (((Fin.castSucc col' : Fin (n + 1)) : ℕ) + 0)) =
      upMoment F ((i' : ℕ) + (col' : ℕ))
    rw [if_pos (by simpa using i'.isLt)]
    simp
  rw [h, hsub, Even.neg_one_pow ⟨n, rfl⟩, one_mul]
  rfl

/-- Coefficients above the `n`-th vanish. -/
theorem hankelOrthoPolynomial_coeff_eq_zero (F : BoundedFabius) (n : ℕ)
    {m : ℕ} (hm : n < m) :
    (hankelOrthoPolynomial F n).coeff m = 0 := by
  rw [hankelOrthoPolynomial, Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    if_neg (by have := j.isLt; omega), mul_zero]

/-- The determinant orthogonal polynomial has degree at most its index. -/
theorem natDegree_hankelOrthoPolynomial_le (F : BoundedFabius) (n : ℕ) :
    (hankelOrthoPolynomial F n).natDegree ≤ n :=
  Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun _ hm =>
    hankelOrthoPolynomial_coeff_eq_zero F n hm

/-- Since the top coefficient `h_n` is positive, the determinant
polynomial has exact degree `n`. -/
theorem natDegree_hankelOrthoPolynomial (F : BoundedFabius)
    (hF : IsFabius F) (n : ℕ) :
    (hankelOrthoPolynomial F n).natDegree = n :=
  le_antisymm (natDegree_hankelOrthoPolynomial_le F n)
    (Polynomial.le_natDegree_of_ne_zero
      (by rw [hankelOrthoPolynomial_coeff_top]
          exact ne_of_gt (hankelDet_pos F hF n)))

/-- The leading coefficient of the determinant orthogonal polynomial is its Hankel determinant. -/
theorem hankelOrthoPolynomial_leadingCoeff (F : BoundedFabius)
    (hF : IsFabius F) (n : ℕ) :
    (hankelOrthoPolynomial F n).leadingCoeff = hankelDet F n := by
  rw [← Polynomial.coeff_natDegree,
    natDegree_hankelOrthoPolynomial F hF n,
    hankelOrthoPolynomial_coeff_top]

/-- Every determinant orthogonal polynomial is nonzero. -/
theorem hankelOrthoPolynomial_ne_zero (F : BoundedFabius)
    (hF : IsFabius F) (n : ℕ) :
    hankelOrthoPolynomial F n ≠ 0 := fun h => by
  have htop := hankelOrthoPolynomial_coeff_top F n
  rw [h, Polynomial.coeff_zero] at htop
  exact ne_of_gt (hankelDet_pos F hF n) htop.symm

/-- The zeroth determinant polynomial is the constant `1`. -/
theorem hankelOrthoPolynomial_zero (F : BoundedFabius) :
    hankelOrthoPolynomial F 0 = 1 := by
  rw [hankelOrthoPolynomial, Fin.sum_univ_one]
  simp [Matrix.det_fin_zero, Fin.val_last]

end PolynomialForm

section PolynomialOrthogonality

/-- Every polynomial is integrable against the up-measure. -/
theorem integrable_polynomial_eval_rvachevMeasure (F : BoundedFabius)
    (hF : IsFabius F) (q : Polynomial ℝ) :
    Integrable (fun x => q.eval x) (rvachevMeasure F) := by
  have h : (fun x : ℝ => q.eval x) = fun x : ℝ =>
      ∑ j ∈ Finset.range (q.natDegree + 1), q.coeff j * x ^ j := by
    funext x
    rw [Polynomial.eval_eq_sum_range]
  rw [h]
  exact integrable_finsetSum _ fun j _ =>
    (integrable_pow_rvachevMeasure F hF j).const_mul _

/-- A determinant orthogonal polynomial times any monomial is integrable. -/
theorem integrable_hankelOrthoValue_mul_pow (F : BoundedFabius)
    (hF : IsFabius F) (n j' : ℕ) :
    Integrable (fun x => hankelOrthoValue F n x * x ^ j')
      (rvachevMeasure F) := by
  have h : (fun x : ℝ => hankelOrthoValue F n x * x ^ j') =
      fun x : ℝ =>
        (hankelOrthoPolynomial F n * Polynomial.X ^ j').eval x := by
    funext x
    rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      hankelOrthoPolynomial_eval]
  rw [h]
  exact integrable_polynomial_eval_rvachevMeasure F hF _

/-- **Orthogonality against all lower-degree polynomials**: the
determinant polynomial annihilates every polynomial of degree `< n`. -/
theorem integral_hankelOrthoValue_mul_eval (F : BoundedFabius)
    (hF : IsFabius F) (n : ℕ) (q : Polynomial ℝ)
    (hq : q.natDegree < n) :
    ∫ x, hankelOrthoValue F n x * q.eval x ∂(rvachevMeasure F) = 0 := by
  have hexp : (fun x : ℝ => hankelOrthoValue F n x * q.eval x) =
      fun x : ℝ => ∑ j ∈ Finset.range (q.natDegree + 1),
        q.coeff j * (hankelOrthoValue F n x * x ^ j) := by
    funext x
    rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hexp, integral_finsetSum _ fun j _ =>
    (integrable_hankelOrthoValue_mul_pow F hF n j).const_mul _]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [MeasureTheory.integral_const_mul,
    integral_hankelOrthoValue_mul_pow F hF n
      (lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hq),
    mul_zero]

end PolynomialOrthogonality

section MonicNormalization

/-- The monic orthogonal polynomial `P_n = h_n⁻¹·(h_nP_n)` of the
up-measure. -/
noncomputable def upOrthoPolynomial (F : BoundedFabius) (n : ℕ) :
    Polynomial ℝ :=
  Polynomial.C (hankelDet F n)⁻¹ * hankelOrthoPolynomial F n

/-- Evaluation of the monic orthogonal polynomial is the normalized determinant value. -/
theorem upOrthoPolynomial_eval (F : BoundedFabius) (n : ℕ) (x : ℝ) :
    (upOrthoPolynomial F n).eval x =
      (hankelDet F n)⁻¹ * hankelOrthoValue F n x := by
  rw [upOrthoPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    hankelOrthoPolynomial_eval]

/-- The zeroth monic orthogonal polynomial is one. -/
theorem upOrthoPolynomial_zero (F : BoundedFabius) :
    upOrthoPolynomial F 0 = 1 := by
  rw [upOrthoPolynomial, hankelOrthoPolynomial_zero, hankelDet_zero]
  norm_num

/-- The monic orthogonal polynomial has degree equal to its index. -/
theorem natDegree_upOrthoPolynomial (F : BoundedFabius)
    (hF : IsFabius F) (n : ℕ) :
    (upOrthoPolynomial F n).natDegree = n := by
  rw [upOrthoPolynomial,
    Polynomial.natDegree_C_mul
      (inv_ne_zero (ne_of_gt (hankelDet_pos F hF n))),
    natDegree_hankelOrthoPolynomial F hF n]

/-- The normalized orthogonal polynomial is monic. -/
theorem upOrthoPolynomial_monic (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) : (upOrthoPolynomial F n).Monic := by
  have hne : hankelDet F n ≠ 0 := ne_of_gt (hankelDet_pos F hF n)
  have hlc : (upOrthoPolynomial F n).leadingCoeff = 1 := by
    rw [upOrthoPolynomial, Polynomial.leadingCoeff_mul,
      Polynomial.leadingCoeff_C,
      hankelOrthoPolynomial_leadingCoeff F hF n, inv_mul_cancel₀ hne]
  exact hlc

/-- Orthogonality of the monic polynomials against all lower-degree
polynomials. -/
theorem integral_upOrthoPolynomial_mul_eval (F : BoundedFabius)
    (hF : IsFabius F) (n : ℕ) (q : Polynomial ℝ)
    (hq : q.natDegree < n) :
    ∫ x, (upOrthoPolynomial F n).eval x * q.eval x
      ∂(rvachevMeasure F) = 0 := by
  have h : (fun x : ℝ => (upOrthoPolynomial F n).eval x * q.eval x) =
      fun x : ℝ =>
        (hankelDet F n)⁻¹ * (hankelOrthoValue F n x * q.eval x) := by
    funext x
    rw [upOrthoPolynomial_eval]
    ring
  rw [h, MeasureTheory.integral_const_mul,
    integral_hankelOrthoValue_mul_eval F hF n q hq, mul_zero]

/-- The monic polynomial against its own leading monomial integrates
to the Hankel ratio `a_n = h_{n+1}/h_n`. -/
theorem integral_upOrthoPolynomial_mul_pow_self (F : BoundedFabius)
    (hF : IsFabius F) (n : ℕ) :
    ∫ x, (upOrthoPolynomial F n).eval x * x ^ n
      ∂(rvachevMeasure F) = hankelRatio F n := by
  have h : (fun x : ℝ => (upOrthoPolynomial F n).eval x * x ^ n) =
      fun x : ℝ =>
        (hankelDet F n)⁻¹ * (hankelOrthoValue F n x * x ^ n) := by
    funext x
    rw [upOrthoPolynomial_eval]
    ring
  rw [h, MeasureTheory.integral_const_mul,
    integral_hankelOrthoValue_mul_pow_self F hF n]
  show (hankelDet F n)⁻¹ * hankelDet F (n + 1) =
    hankelDet F (n + 1) / hankelDet F n
  rw [div_eq_inv_mul]

/-- **The norm identity**: `∫ P_n(x)² dμ_up = a_n = h_{n+1}/h_n` ---
the squared `L²`-norm of the `n`-th monic orthogonal polynomial is the
Hankel-determinant ratio. -/
theorem integral_upOrthoPolynomial_sq (F : BoundedFabius)
    (hF : IsFabius F) (n : ℕ) :
    ∫ x, (upOrthoPolynomial F n).eval x ^ 2 ∂(rvachevMeasure F) =
      hankelRatio F n := by
  have hint : ∀ p q : Polynomial ℝ,
      Integrable (fun x => p.eval x * q.eval x) (rvachevMeasure F) := by
    intro p q
    have h := integrable_polynomial_eval_rvachevMeasure F hF (p * q)
    simpa [Polynomial.eval_mul] using h
  have hint2 : Integrable
      (fun x => (upOrthoPolynomial F n).eval x * x ^ n)
      (rvachevMeasure F) := by
    have h := hint (upOrthoPolynomial F n) (Polynomial.X ^ n)
    simpa [Polynomial.eval_pow] using h
  have hdiff : ∫ x, (upOrthoPolynomial F n).eval x *
      (upOrthoPolynomial F n - Polynomial.X ^ n).eval x
      ∂(rvachevMeasure F) = 0 := by
    cases n with
    | zero =>
      have h0 : upOrthoPolynomial F 0 - Polynomial.X ^ 0 = 0 := by
        rw [upOrthoPolynomial_zero, pow_zero, sub_self]
      rw [h0]
      simp
    | succ m =>
      refine integral_upOrthoPolynomial_mul_eval F hF (m + 1) _
        (lt_of_le_of_lt (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
          fun N hN => ?_) (Nat.lt_succ_self m))
      rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
      rcases Nat.lt_or_ge (m + 1) N with hN' | hN'
      · rw [if_neg (by omega), upOrthoPolynomial,
          Polynomial.coeff_C_mul,
          hankelOrthoPolynomial_coeff_eq_zero F (m + 1) hN', mul_zero,
          sub_zero]
      · have hNe : N = m + 1 := by omega
        subst hNe
        rw [if_pos rfl]
        have hc : (upOrthoPolynomial F (m + 1)).coeff (m + 1) = 1 := by
          have h := Polynomial.Monic.coeff_natDegree
            (upOrthoPolynomial_monic F hF (m + 1))
          rwa [natDegree_upOrthoPolynomial F hF (m + 1)] at h
        rw [hc]
        exact sub_self 1
  have hsplit : (fun x : ℝ => (upOrthoPolynomial F n).eval x ^ 2) =
      fun x : ℝ => (upOrthoPolynomial F n).eval x *
          (upOrthoPolynomial F n - Polynomial.X ^ n).eval x +
        (upOrthoPolynomial F n).eval x * x ^ n := by
    funext x
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    ring
  rw [hsplit, MeasureTheory.integral_add (hint _ _) hint2, hdiff,
    zero_add, integral_upOrthoPolynomial_mul_pow_self F hF n]

end MonicNormalization

section Uniqueness

/-- **Positivity of squared mass**: a nonzero polynomial has positive
`L²`-norm against the up-measure — the measure charges `(-1,1)` fully
and annihilates the finite root set. -/
theorem integral_sq_eval_pos (F : BoundedFabius) (hF : IsFabius F)
    {q : Polynomial ℝ} (hq : q ≠ 0) :
    0 < ∫ x, q.eval x ^ 2 ∂(rvachevMeasure F) := by
  have hnonneg : 0 ≤ᵐ[rvachevMeasure F] fun t : ℝ => q.eval t ^ 2 :=
    Filter.Eventually.of_forall fun t => sq_nonneg _
  have hint : Integrable (fun t : ℝ => q.eval t ^ 2)
      (rvachevMeasure F) := by
    have h := integrable_polynomial_eval_rvachevMeasure F hF (q * q)
    simpa [Polynomial.eval_mul, pow_two] using h
  rw [integral_pos_iff_support_of_nonneg_ae hnonneg hint]
  have hsupp : Set.Ioo (-1 : ℝ) 1 \ {t : ℝ | q.IsRoot t} ⊆
      Function.support fun t : ℝ => q.eval t ^ 2 := by
    intro t ht
    simp only [Function.mem_support]
    intro h0
    refine ht.2 ?_
    show q.IsRoot t
    rw [Polynomial.IsRoot]
    exact (pow_eq_zero_iff two_ne_zero).mp h0
  refine lt_of_lt_of_le ?_ (measure_mono hsupp)
  rw [measure_sdiff_null (rvachevMeasure_finite_eq_zero F
      (Polynomial.finite_setOf_isRoot hq)),
    rvachevMeasure_Ioo_eq_one F hF]
  exact zero_lt_one

/-- A polynomial orthogonal to all monomials below `n` annihilates
every polynomial of degree `< n`. -/
theorem integral_mul_eval_eq_zero_of_forall_pow (F : BoundedFabius)
    (hF : IsFabius F) {n : ℕ} {s : Polynomial ℝ}
    (hs : ∀ j < n, ∫ x, s.eval x * x ^ j ∂(rvachevMeasure F) = 0)
    {q : Polynomial ℝ} (hq : q.natDegree < n) :
    ∫ x, s.eval x * q.eval x ∂(rvachevMeasure F) = 0 := by
  have hintpow : ∀ j : ℕ, Integrable
      (fun x : ℝ => s.eval x * x ^ j) (rvachevMeasure F) := by
    intro j
    have h := integrable_polynomial_eval_rvachevMeasure F hF
      (s * Polynomial.X ^ j)
    simpa [Polynomial.eval_mul, Polynomial.eval_pow] using h
  have hexp : (fun x : ℝ => s.eval x * q.eval x) =
      fun x : ℝ => ∑ j ∈ Finset.range (q.natDegree + 1),
        q.coeff j * (s.eval x * x ^ j) := by
    funext x
    have hq' := Polynomial.eval_eq_sum_range (p := q) x
    rw [hq', Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hexp, integral_finsetSum _ fun j _ => (hintpow j).const_mul _]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [MeasureTheory.integral_const_mul,
    hs j (lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
      hq),
    mul_zero]

/-- **Uniqueness of the monic orthogonal polynomials**: a monic
polynomial of degree `n` orthogonal to all lower monomials *is* the
`n`-th orthogonal polynomial of the up-measure. -/
theorem eq_upOrthoPolynomial_of_monic_of_orthogonal
    (F : BoundedFabius) (hF : IsFabius F) {n : ℕ} {q : Polynomial ℝ}
    (hmon : q.Monic) (hdeg : q.natDegree = n)
    (horth : ∀ j < n, ∫ x, q.eval x * x ^ j ∂(rvachevMeasure F) = 0) :
    q = upOrthoPolynomial F n := by
  by_contra hne
  set d : Polynomial ℝ := q - upOrthoPolynomial F n with hd
  have hdne : d ≠ 0 := sub_ne_zero.mpr hne
  have hcoeffs : ∀ m : ℕ, n ≤ m → d.coeff m = 0 := by
    intro m hm
    rw [hd, Polynomial.coeff_sub]
    rcases eq_or_lt_of_le hm with hEq | hlt
    · rw [← hEq]
      have h1 : q.coeff n = 1 := by
        have h := hmon.coeff_natDegree
        rwa [hdeg] at h
      have h2 : (upOrthoPolynomial F n).coeff n = 1 := by
        have h := (upOrthoPolynomial_monic F hF n).coeff_natDegree
        rwa [natDegree_upOrthoPolynomial F hF n] at h
      rw [h1, h2, sub_self]
    · have h1 : q.coeff m = 0 := by
        refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
        rw [hdeg]
        exact hlt
      have h2 : (upOrthoPolynomial F n).coeff m = 0 := by
        refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
        rw [natDegree_upOrthoPolynomial F hF n]
        exact hlt
      rw [h1, h2, sub_zero]
  have hdorth : ∀ j < n,
      ∫ x, d.eval x * x ^ j ∂(rvachevMeasure F) = 0 := by
    intro j hj
    have hsub : (fun x : ℝ => d.eval x * x ^ j) = fun x : ℝ =>
        q.eval x * x ^ j -
          (upOrthoPolynomial F n).eval x * x ^ j := by
      funext x
      rw [hd, Polynomial.eval_sub]
      ring
    have hint1 : Integrable (fun x : ℝ => q.eval x * x ^ j)
        (rvachevMeasure F) := by
      have h := integrable_polynomial_eval_rvachevMeasure F hF
        (q * Polynomial.X ^ j)
      simpa [Polynomial.eval_mul, Polynomial.eval_pow] using h
    have hint2 : Integrable
        (fun x : ℝ => (upOrthoPolynomial F n).eval x * x ^ j)
        (rvachevMeasure F) := by
      have h := integrable_polynomial_eval_rvachevMeasure F hF
        (upOrthoPolynomial F n * Polynomial.X ^ j)
      simpa [Polynomial.eval_mul, Polynomial.eval_pow] using h
    have hPn : ∫ x, (upOrthoPolynomial F n).eval x * x ^ j
        ∂(rvachevMeasure F) = 0 := by
      have h := integral_upOrthoPolynomial_mul_eval F hF n
        (Polynomial.X ^ j)
        (by simpa [Polynomial.natDegree_X_pow] using hj)
      simpa [Polynomial.eval_pow] using h
    rw [hsub, MeasureTheory.integral_sub hint1 hint2, horth j hj, hPn,
      sub_zero]
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    exact hdne (Polynomial.ext fun m => by
      simpa using hcoeffs m (Nat.zero_le m))
  · have hdlt : d.natDegree < n := by
      have hle : d.natDegree ≤ n - 1 :=
        Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN =>
          hcoeffs N (by omega)
      omega
    have hzero : ∫ x, d.eval x * d.eval x ∂(rvachevMeasure F) = 0 :=
      integral_mul_eval_eq_zero_of_forall_pow F hF hdorth hdlt
    have hzero' : ∫ x, d.eval x ^ 2 ∂(rvachevMeasure F) = 0 := by
      have hfun : (fun x : ℝ => d.eval x ^ 2) =
          fun x : ℝ => d.eval x * d.eval x := funext fun x => by ring
      rw [hfun]
      exact hzero
    exact absurd hzero' (ne_of_gt (integral_sq_eval_pos F hF hdne))

end Uniqueness

section Symmetry

open scoped ENNReal NNReal

/-- The up-measure is negation-invariant at the level of integrals:
the density is even and Lebesgue measure is negation-invariant. -/
theorem integral_comp_neg_rvachevMeasure (F : BoundedFabius)
    (hF : IsFabius F) (f : ℝ → ℝ) :
    ∫ x, f (-x) ∂(rvachevMeasure F) =
      ∫ x, f x ∂(rvachevMeasure F) := by
  have hbridge : ∀ g : ℝ → ℝ, ∫ x, g x ∂(rvachevMeasure F) =
      ∫ x, g x * rvachevUp F x := by
    intro g
    rw [rvachevMeasure]
    have hcoe : (fun x : ℝ => ENNReal.ofReal (rvachevUp F x)) =
        fun x => ((rvachevUp F x).toNNReal : ℝ≥0∞) :=
      funext fun x => rfl
    rw [hcoe, integral_withDensity_eq_integral_smul
      ((rvachev_contDiff F hF).continuous.measurable.real_toNNReal)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [NNReal.smul_def, Real.coe_toNNReal _ (rvachevUp_nonneg F x),
      smul_eq_mul, mul_comm]
  rw [hbridge (fun x => f (-x)), hbridge f]
  calc ∫ x, f (-x) * rvachevUp F x
      = ∫ x, f (-x) * rvachevUp F (-x) := by
        refine integral_congr_ae
          (Filter.Eventually.of_forall fun x => ?_)
        dsimp only
        rw [rvachevUp_even F x]
    _ = ∫ x, f x * rvachevUp F x :=
        integral_neg_eq_self (fun x => f x * rvachevUp F x) _

end Symmetry

end Fabius
