import PolynomialFormulas.GaussianRadicals
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Encodable.Pi

/-!
# Executable bounded polynomials over the Gaussian rationals

This file is the computational coefficient layer for certified root
approximation.  A polynomial of degree at most `n` is represented by the
literal vector of its `n + 1` Gaussian-rational coefficients, in increasing
order.  Every coefficient algorithm and every definition returning rational
data is executable.  The explicitly marked complex helpers are theorem-side
semantic bridges only; no executable coefficient routine depends on them.

`QPoly.toPolynomial` and `QPoly.toComplexPolynomial` are semantic bridges to
mathlib polynomials.  The arithmetic operations themselves manipulate only
finite vectors and Gaussian rationals.
-/

namespace LeanProofs.PolynomialFormulas

/-! ## Effective coding of Gaussian rationals -/

namespace GaussianRat

/-- The coordinate equivalence used to encode Gaussian rationals. -/
def equivRatPair : GaussianRat ≃ ℚ × ℚ where
  toFun z := (z.re, z.im)
  invFun z := ⟨z.1, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Gaussian rationals are effectively encodable by pairs of rationals. -/
instance : Encodable GaussianRat :=
  Encodable.ofEquiv (ℚ × ℚ) equivRatPair

/-- The exact rational Manhattan norm `|re z| + |im z|`. -/
def l1 (z : GaussianRat) : ℚ := |z.re| + |z.im|

/-- The exact rational maximum-coordinate norm. -/
def linf (z : GaussianRat) : ℚ := max |z.re| |z.im|

/-- Exact Manhattan distance on Gaussian rationals. -/
def manhattan (z w : GaussianRat) : ℚ := l1 (z - w)

@[simp] theorem l1_mk (a b : ℚ) : l1 (⟨a, b⟩ : GaussianRat) = |a| + |b| := rfl

@[simp] theorem linf_mk (a b : ℚ) : linf (⟨a, b⟩ : GaussianRat) = max |a| |b| := rfl

theorem l1_nonneg (z : GaussianRat) : 0 ≤ l1 z := by
  exact add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem linf_nonneg (z : GaussianRat) : 0 ≤ linf z := by
  exact (abs_nonneg z.re).trans (le_max_left _ _)

theorem linf_le_l1 (z : GaussianRat) : linf z ≤ l1 z := by
  exact max_le (le_add_of_nonneg_right (abs_nonneg z.im))
    (le_add_of_nonneg_left (abs_nonneg z.re))

/-- The Manhattan norm is at most twice the maximum-coordinate norm. -/
theorem l1_le_two_linf (z : GaussianRat) : l1 z ≤ 2 * linf z := by
  unfold l1 linf
  linarith [le_max_left |z.re| |z.im|, le_max_right |z.re| |z.im|]

@[simp] theorem l1_eq_zero {z : GaussianRat} : l1 z = 0 ↔ z = 0 := by
  constructor
  · intro h
    change |z.re| + |z.im| = 0 at h
    have hreAbs : |z.re| = 0 := by
      linarith [abs_nonneg z.re, abs_nonneg z.im]
    have himAbs : |z.im| = 0 := by
      linarith [abs_nonneg z.re, abs_nonneg z.im]
    have hre : z.re = 0 := abs_eq_zero.mp hreAbs
    have him : z.im = 0 := abs_eq_zero.mp himAbs
    exact QuadraticAlgebra.ext hre him
  · rintro rfl
    simp [l1]

theorem l1_add_le (z w : GaussianRat) : l1 (z + w) ≤ l1 z + l1 w := by
  simp only [l1, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
  linarith [abs_add_le z.re w.re, abs_add_le z.im w.im]

theorem l1_neg (z : GaussianRat) : l1 (-z) = l1 z := by
  simp [l1]

theorem l1_sub_le (z w : GaussianRat) : l1 (z - w) ≤ l1 z + l1 w := by
  simpa [sub_eq_add_neg, l1_neg] using l1_add_le z (-w)

theorem manhattan_nonneg (z w : GaussianRat) : 0 ≤ manhattan z w := l1_nonneg _

@[simp] theorem manhattan_self (z : GaussianRat) : manhattan z z = 0 := by
  simp [manhattan]

@[simp] theorem manhattan_eq_zero {z w : GaussianRat} : manhattan z w = 0 ↔ z = w := by
  simp [manhattan, sub_eq_zero]

theorem manhattan_symm (z w : GaussianRat) : manhattan z w = manhattan w z := by
  rw [manhattan, manhattan, ← neg_sub, l1_neg]

theorem manhattan_triangle (x y z : GaussianRat) :
    manhattan x z ≤ manhattan x y + manhattan y z := by
  rw [manhattan, manhattan, manhattan]
  have hxyz : (x - y) + (y - z) = x - z := by abel
  rw [← hxyz]
  exact l1_add_le (x - y) (y - z)

/-- Manhattan distance on semantic complex values. -/
def complexManhattan (z w : ℂ) : ℝ := |(z - w).re| + |(z - w).im|

@[simp] theorem toComplex_re (z : GaussianRat) : (toComplex z).re = z.re := by
  simp [toComplex_apply]

@[simp] theorem toComplex_im (z : GaussianRat) : (toComplex z).im = z.im := by
  simp [toComplex_apply]

theorem complexManhattan_toComplex (z w : GaussianRat) :
    complexManhattan (toComplex z) (toComplex w) = (manhattan z w : ℝ) := by
  simp [complexManhattan, manhattan, l1, Rat.cast_add, Rat.cast_abs]

theorem norm_toComplex_le_l1 (z : GaussianRat) :
    ‖toComplex z‖ ≤ (l1 z : ℝ) := by
  calc
    ‖toComplex z‖ ≤ |(toComplex z).re| + |(toComplex z).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = (l1 z : ℝ) := by simp [l1, Rat.cast_add, Rat.cast_abs]

theorem linf_toComplex_le_norm (z : GaussianRat) :
    (linf z : ℝ) ≤ ‖toComplex z‖ := by
  calc
    (linf z : ℝ) = max |(toComplex z).re| |(toComplex z).im| := by
      simp [linf, Rat.cast_max, Rat.cast_abs]
    _ ≤ ‖toComplex z‖ := max_le (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _)

/-- Euclidean norm is at most twice the rational maximum-coordinate norm. -/
theorem norm_toComplex_le_two_linf (z : GaussianRat) :
    ‖toComplex z‖ ≤ (2 * linf z : ℚ) := by
  exact (norm_toComplex_le_l1 z).trans (by exact_mod_cast l1_le_two_linf z)

/-- Manhattan distance in `ℂ` is bounded by twice Euclidean distance. -/
theorem complexManhattan_le_two_dist (z w : ℂ) :
    complexManhattan z w ≤ 2 * dist z w := by
  rw [show dist z w = ‖z - w‖ by exact dist_eq_norm z w]
  unfold complexManhattan
  linarith [Complex.abs_re_le_norm (z - w), Complex.abs_im_le_norm (z - w)]

end GaussianRat

/-! ## Fixed coefficient vectors -/

namespace GaussianPolynomialApproximationCore

/-- Coefficients of a polynomial of degree at most `n`, stored from constant
coefficient through coefficient `n`. -/
abbrev QPoly (n : ℕ) := Fin (n + 1) → GaussianRat

abbrev QPoly0 := QPoly 0
abbrev QPoly1 := QPoly 1
abbrev QPoly2 := QPoly 2
abbrev QPoly3 := QPoly 3
abbrev QPoly4 := QPoly 4
abbrev QPoly5 := QPoly 5
abbrev QPoly6 := QPoly 6
abbrev QPoly7 := QPoly 7
abbrev QPoly8 := QPoly 8

namespace QPoly

/-- The `i`th coefficient, extended by zero beyond the vector bound. -/
def coeff {n : ℕ} (p : QPoly n) (i : ℕ) : GaussianRat :=
  if h : i < n + 1 then p ⟨i, h⟩ else 0

@[simp] theorem coeff_apply {n : ℕ} (p : QPoly n) (i : Fin (n + 1)) :
    coeff p i = p i := by
  simp [coeff, i.isLt]

theorem coeff_eq_zero_of_bound_lt {n i : ℕ} (p : QPoly n) (h : n < i) :
    coeff p i = 0 := by
  simp [coeff, Nat.not_lt.mpr (Nat.succ_le_iff.mpr h)]

/-- Convert a fixed coefficient vector to the corresponding mathlib
polynomial. -/
def support {n : ℕ} (p : QPoly n) : Finset ℕ :=
  (Finset.range (n + 1)).filter fun i => coeff p i ≠ 0

/-- The raw finitely-supported coefficient function.  It is constructed with
the available decidable equality on Gaussian rationals, rather than
`Classical.decEq`. -/
def toFinsupp {n : ℕ} (p : QPoly n) : ℕ →₀ GaussianRat where
  support := support p
  toFun := coeff p
  mem_support_toFun i := by
    simp only [support, Finset.mem_filter, Finset.mem_range]
    constructor
    · exact And.right
    · intro hi
      exact ⟨by
        by_contra hbound
        have : coeff p i = 0 := by simp [coeff, hbound]
        exact hi this, hi⟩

def toPolynomial {n : ℕ} (p : QPoly n) : Polynomial GaussianRat :=
  ⟨AddMonoidAlgebra.ofCoeff (toFinsupp p)⟩

/-- Read the first `n + 1` coefficients of a mathlib polynomial. -/
def ofPolynomial (n : ℕ) (p : Polynomial GaussianRat) : QPoly n :=
  fun i => p.coeff i

@[simp] theorem coeff_toPolynomial {n i : ℕ} (p : QPoly n) :
    (toPolynomial p).coeff i = coeff p i := by
  rfl

@[simp] theorem support_toPolynomial {n : ℕ} (p : QPoly n) :
    (toPolynomial p).support = support p := rfl

@[simp] theorem ofPolynomial_apply {n : ℕ} (p : Polynomial GaussianRat)
    (i : Fin (n + 1)) : ofPolynomial n p i = p.coeff i := rfl

theorem natDegree_toPolynomial_le {n : ℕ} (p : QPoly n) :
    (toPolynomial p).natDegree ≤ n := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro i hi
  rw [coeff_toPolynomial]
  exact coeff_eq_zero_of_bound_lt p hi

theorem toPolynomial_ofPolynomial {n : ℕ} {p : Polynomial GaussianRat}
    (h : p.natDegree ≤ n) : toPolynomial (ofPolynomial n p) = p := by
  apply Polynomial.ext
  intro i
  by_cases hi : i < n + 1
  · rw [coeff_toPolynomial]
    simp [coeff, ofPolynomial, hi]
  · have hni : p.natDegree < i := lt_of_le_of_lt h (Nat.lt_of_not_ge (by omega))
    rw [coeff_toPolynomial]
    simp [coeff, hi, Polynomial.coeff_eq_zero_of_natDegree_lt hni]

theorem toPolynomial_injective {n : ℕ} :
    Function.Injective (toPolynomial : QPoly n → Polynomial GaussianRat) := by
  intro p q hpq
  funext i
  have hcoeff := congrArg (fun r : Polynomial GaussianRat => r.coeff i) hpq
  simpa using hcoeff

/-- The zero coefficient vector. -/
def zero (n : ℕ) : QPoly n := fun _ => 0

/-- The constant-one coefficient vector. -/
def one (n : ℕ) : QPoly n := fun i => if i.val = 0 then 1 else 0

@[simp] theorem toPolynomial_zero (n : ℕ) : toPolynomial (zero n) = 0 := by
  apply Polynomial.ext
  intro i
  simp [zero, coeff]

@[simp] theorem toPolynomial_one (n : ℕ) : toPolynomial (one n) = 1 := by
  apply Polynomial.ext
  intro i
  rcases i with _ | i <;> simp [one, coeff, Polynomial.coeff_one]

/-- Pointwise addition at a common degree bound. -/
def add {n : ℕ} (p q : QPoly n) : QPoly n := fun i => p i + q i

/-- Pointwise negation. -/
def neg {n : ℕ} (p : QPoly n) : QPoly n := fun i => -p i

/-- Pointwise subtraction at a common degree bound. -/
def sub {n : ℕ} (p q : QPoly n) : QPoly n := fun i => p i - q i

/-- Scalar multiplication of all coefficients. -/
def scale {n : ℕ} (a : GaussianRat) (p : QPoly n) : QPoly n := fun i => a * p i

@[simp] theorem coeff_add {n i : ℕ} (p q : QPoly n) :
    coeff (add p q) i = coeff p i + coeff q i := by
  by_cases hi : i < n + 1 <;> simp [coeff, add, hi]

@[simp] theorem coeff_neg {n i : ℕ} (p : QPoly n) :
    coeff (neg p) i = -coeff p i := by
  by_cases hi : i < n + 1 <;> simp [coeff, neg, hi]

@[simp] theorem coeff_sub {n i : ℕ} (p q : QPoly n) :
    coeff (sub p q) i = coeff p i - coeff q i := by
  by_cases hi : i < n + 1 <;> simp [coeff, sub, hi]

@[simp] theorem coeff_scale {n i : ℕ} (a : GaussianRat) (p : QPoly n) :
    coeff (scale a p) i = a * coeff p i := by
  by_cases hi : i < n + 1 <;> simp [coeff, scale, hi]

@[simp] theorem toPolynomial_add {n : ℕ} (p q : QPoly n) :
    toPolynomial (add p q) = toPolynomial p + toPolynomial q := by
  apply Polynomial.ext
  intro i
  simp

@[simp] theorem toPolynomial_neg {n : ℕ} (p : QPoly n) :
    toPolynomial (neg p) = -toPolynomial p := by
  apply Polynomial.ext
  intro i
  simp

@[simp] theorem toPolynomial_sub {n : ℕ} (p q : QPoly n) :
    toPolynomial (sub p q) = toPolynomial p - toPolynomial q := by
  apply Polynomial.ext
  intro i
  simp

@[simp] theorem toPolynomial_scale {n : ℕ} (a : GaussianRat) (p : QPoly n) :
    toPolynomial (scale a p) = Polynomial.C a * toPolynomial p := by
  apply Polynomial.ext
  intro i
  simp [Polynomial.coeff_C_mul]

/-- Convolution product.  The result has the exact static degree bound
`n + m`. -/
def mul {n m : ℕ} (p : QPoly n) (q : QPoly m) : QPoly (n + m) :=
  fun k => ∑ ij ∈ Finset.antidiagonal (k : ℕ), coeff p ij.1 * coeff q ij.2

@[simp] theorem toPolynomial_mul {n m : ℕ} (p : QPoly n) (q : QPoly m) :
    toPolynomial (mul p q) = toPolynomial p * toPolynomial q := by
  apply Polynomial.ext
  intro k
  by_cases hk : k < n + m + 1
  · rw [coeff_toPolynomial, Polynomial.coeff_mul]
    simp [coeff_toPolynomial, coeff, hk, mul]
  · have hprod : (toPolynomial p * toPolynomial q).coeff k = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      exact lt_of_le_of_lt
        (Polynomial.natDegree_mul_le_of_le
          (natDegree_toPolynomial_le p) (natDegree_toPolynomial_le q))
        (by omega)
    rw [coeff_toPolynomial, hprod]
    simp [coeff, hk]

/-- Natural powers, with static degree bound `n * k`. -/
def pow {n : ℕ} (p : QPoly n) : (k : ℕ) → QPoly (n * k)
  | 0 => one 0
  | k + 1 => mul (pow p k) p

@[simp] theorem toPolynomial_pow {n : ℕ} (p : QPoly n) (k : ℕ) :
    toPolynomial (pow p k) = toPolynomial p ^ k := by
  induction k with
  | zero => simp [pow]
  | succ k ih => simp [pow, ih, pow_succ]

/-- Formal derivative, retaining the sharp static bound `n - 1`. -/
def derivative {n : ℕ} (p : QPoly n) : QPoly (n - 1) :=
  fun i => coeff p (i + 1) * (i + 1 : ℕ)

@[simp] theorem toPolynomial_derivative {n : ℕ} (p : QPoly n) :
    toPolynomial (derivative p) = (toPolynomial p).derivative := by
  apply Polynomial.ext
  intro i
  rw [coeff_toPolynomial, Polynomial.coeff_derivative, coeff_toPolynomial]
  by_cases hi : i < n - 1 + 1
  · simp [derivative, coeff, hi]
  · have hlhs : coeff (derivative p) i = 0 := by simp [coeff, hi]
    rw [hlhs]
    have hpzero : coeff p (i + 1) = 0 := by
      apply coeff_eq_zero_of_bound_lt
      omega
    simp [hpzero]

/-- Multiply by `X^k`, shifting coefficient indices upward by `k`. -/
def indexShift {n : ℕ} (k : ℕ) (p : QPoly n) : QPoly (n + k) :=
  fun i => if _h : k ≤ i then coeff p (i - k) else 0

@[simp] theorem toPolynomial_indexShift {n : ℕ} (k : ℕ) (p : QPoly n) :
    toPolynomial (indexShift k p) = toPolynomial p * Polynomial.X ^ k := by
  apply Polynomial.ext
  intro i
  rw [coeff_toPolynomial, Polynomial.coeff_mul_X_pow']
  by_cases hi : i < n + k + 1 <;> by_cases hki : k ≤ i
  · simp [coeff, indexShift, hi, hki]
  · simp [coeff, indexShift, hi, hki]
  · have hbound : ¬i - k < n + 1 := by omega
    simp [coeff, hi, hki, hbound]
  · simp [coeff, hi, hki]

/-- Substitute `X + a` for `X`, without changing the static degree bound. -/
def translate {n : ℕ} (a : GaussianRat) (p : QPoly n) : QPoly n :=
  fun j => ∑ k ∈ Finset.range (n + 1),
    ((k + j).choose j : ℕ) * coeff p (k + j) * a ^ k

@[simp] theorem toPolynomial_translate {n : ℕ} (a : GaussianRat) (p : QPoly n) :
    toPolynomial (translate a p) = Polynomial.taylor a (toPolynomial p) := by
  apply Polynomial.ext
  intro j
  by_cases hj : j < n + 1
  · rw [coeff_toPolynomial, Polynomial.taylor_coeff]
    have hdeg : (Polynomial.hasseDeriv j (toPolynomial p)).natDegree < n + 1 :=
      lt_of_le_of_lt
        ((Polynomial.natDegree_hasseDeriv_le _ _).trans
          (Nat.sub_le _ _)) (Nat.lt_succ_iff.mpr (natDegree_toPolynomial_le p))
    rw [Polynomial.eval_eq_sum_range' hdeg]
    simp only [Polynomial.hasseDeriv_coeff, coeff_toPolynomial]
    simp [coeff, translate, hj]
  · have hlhs : (toPolynomial (translate a p)).coeff j = 0 := by
      rw [coeff_toPolynomial]
      simp [coeff, hj]
    rw [hlhs]
    symm
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    rw [Polynomial.natDegree_taylor]
    exact lt_of_le_of_lt (natDegree_toPolynomial_le p) (by omega)

/-! ## Executable degree and evaluation -/

/-- Whether all stored coefficients are zero. -/
def isZero {n : ℕ} (p : QPoly n) : Bool := decide (support p = ∅)

theorem support_eq_empty_iff {n : ℕ} {p : QPoly n} :
    support p = ∅ ↔ p = zero n := by
  constructor
  · intro hs
    funext i
    by_contra hi
    change p i ≠ 0 at hi
    have himem : (i : ℕ) ∈ support p := by
      simp only [support, Finset.mem_filter, Finset.mem_range]
      exact ⟨i.isLt, by simpa [coeff, i.isLt] using hi⟩
    rw [hs] at himem
    exact Finset.notMem_empty _ himem
  · rintro rfl
    ext i
    simp [support, zero, coeff]

/-- Numeric degree, using the convention `degree 0 = 0`.  This is a finite
maximum over the explicitly stored support. -/
def degree {n : ℕ} (p : QPoly n) : ℕ :=
  (support p).max.unbotD 0

/-- Degree with the zero polynomial represented by `none`. -/
def degree? {n : ℕ} (p : QPoly n) : Option ℕ :=
  if support p = ∅ then none else some (degree p)

@[simp] theorem isZero_eq_true {n : ℕ} {p : QPoly n} :
    isZero p = true ↔ p = zero n := by
  simp [isZero, support_eq_empty_iff]

@[simp] theorem degree?_eq_none {n : ℕ} {p : QPoly n} :
    degree? p = none ↔ p = zero n := by
  simp [degree?, support_eq_empty_iff]

theorem degree_eq_natDegree {n : ℕ} (p : QPoly n) :
    degree p = (toPolynomial p).natDegree := by
  simp [degree, Polynomial.natDegree, Polynomial.degree]

theorem degree?_eq_some_natDegree {n : ℕ} {p : QPoly n} (h : p ≠ zero n) :
    degree? p = some (toPolynomial p).natDegree := by
  rw [← degree_eq_natDegree]
  simp [degree?, support_eq_empty_iff, h]

theorem degree_le_bound {n : ℕ} (p : QPoly n) : degree p ≤ n := by
  rw [degree_eq_natDegree]
  exact natDegree_toPolynomial_le p

/-- The coefficient at the executable degree. -/
def leadingCoeff {n : ℕ} (p : QPoly n) : GaussianRat :=
  p ⟨degree p, Nat.lt_succ_iff.mpr (degree_le_bound p)⟩

/-- Executable monicity test. -/
def isMonic {n : ℕ} (p : QPoly n) : Bool := decide (leadingCoeff p = 1)

theorem leadingCoeff_eq_toPolynomial {n : ℕ} (p : QPoly n) :
    leadingCoeff p = (toPolynomial p).leadingCoeff := by
  rw [Polynomial.leadingCoeff, ← degree_eq_natDegree]
  symm
  exact coeff_apply p ⟨degree p, Nat.lt_succ_iff.mpr (degree_le_bound p)⟩

@[simp] theorem isMonic_eq_true {n : ℕ} {p : QPoly n} :
    isMonic p = true ↔ (toPolynomial p).Monic := by
  simp [isMonic, Polynomial.Monic, ← leadingCoeff_eq_toPolynomial]

/-- Exact evaluation in the Gaussian rationals. -/
def eval {n : ℕ} (p : QPoly n) (x : GaussianRat) : GaussianRat :=
  ∑ i ∈ Finset.range (n + 1), coeff p i * x ^ i

theorem eval_eq_toPolynomial_eval {n : ℕ} (p : QPoly n) (x : GaussianRat) :
    eval p x = (toPolynomial p).eval x := by
  rw [Polynomial.eval_eq_sum_range'
    (Nat.lt_succ_iff.mpr (natDegree_toPolynomial_le p))]
  simp only [eval, coeff_toPolynomial]

@[simp] theorem eval_add {n : ℕ} (p q : QPoly n) (x : GaussianRat) :
    eval (add p q) x = eval p x + eval q x := by
  simp [eval, Finset.sum_add_distrib, add_mul]

@[simp] theorem eval_mul {n m : ℕ} (p : QPoly n) (q : QPoly m) (x : GaussianRat) :
    eval (mul p q) x = eval p x * eval q x := by
  simp [eval_eq_toPolynomial_eval]

@[simp] theorem eval_pow {n : ℕ} (p : QPoly n) (k : ℕ) (x : GaussianRat) :
    eval (pow p k) x = eval p x ^ k := by
  simp [eval_eq_toPolynomial_eval]

@[simp] theorem eval_indexShift {n : ℕ} (k : ℕ) (p : QPoly n) (x : GaussianRat) :
    eval (indexShift k p) x = eval p x * x ^ k := by
  simp [eval_eq_toPolynomial_eval]

@[simp] theorem eval_translate {n : ℕ} (a : GaussianRat) (p : QPoly n)
    (x : GaussianRat) : eval (translate a p) x = eval p (x + a) := by
  simp [eval_eq_toPolynomial_eval, Polynomial.taylor_eval]

/-! ## Complex semantic bridge -/

/-- The embedded coefficients with their finite support inherited from the
Gaussian-rational vector.  No equality test on arbitrary complex numbers is
needed. -/
noncomputable def toComplexFinsupp {n : ℕ} (p : QPoly n) : ℕ →₀ ℂ where
  support := support p
  toFun := fun i => GaussianRat.toComplex (coeff p i)
  mem_support_toFun i := by
    rw [GaussianRat.toComplex_ne_zero]
    exact (toFinsupp p).mem_support_toFun i

/-- Map every exact Gaussian-rational coefficient into `ℂ`, retaining the
explicit finite support. -/
noncomputable def toComplexPolynomial {n : ℕ} (p : QPoly n) : Polynomial ℂ :=
  ⟨AddMonoidAlgebra.ofCoeff (toComplexFinsupp p)⟩

@[simp] theorem coeff_toComplexPolynomial {n i : ℕ} (p : QPoly n) :
    (toComplexPolynomial p).coeff i = GaussianRat.toComplex (coeff p i) := by
  rfl

theorem toComplexPolynomial_eq_map {n : ℕ} (p : QPoly n) :
    toComplexPolynomial p =
      (toPolynomial p).map GaussianRat.toComplex.toRingHom := by
  apply Polynomial.ext
  intro i
  simp

/-- Evaluate the embedded coefficient vector at an arbitrary complex point. -/
noncomputable def evalComplex {n : ℕ} (p : QPoly n) (x : ℂ) : ℂ :=
  ∑ i ∈ Finset.range (n + 1), GaussianRat.toComplex (coeff p i) * x ^ i

theorem evalComplex_eq_sum {n : ℕ} (p : QPoly n) (x : ℂ) :
    evalComplex p x =
      ∑ i : Fin (n + 1), GaussianRat.toComplex (p i) * x ^ (i : ℕ) := by
  rw [evalComplex, ← Fin.sum_univ_eq_sum_range]
  simp

theorem evalComplex_eq_toComplexPolynomial_eval {n : ℕ} (p : QPoly n) (x : ℂ) :
    evalComplex p x = (toComplexPolynomial p).eval x := by
  have hdeg : (toComplexPolynomial p).natDegree < n + 1 :=
    by
      rw [toComplexPolynomial_eq_map]
      exact lt_of_le_of_lt Polynomial.natDegree_map_le
        (Nat.lt_succ_iff.mpr (natDegree_toPolynomial_le p))
  rw [Polynomial.eval_eq_sum_range' hdeg]
  rw [evalComplex]
  apply Finset.sum_congr rfl
  intro i hi
  simp [coeff, Finset.mem_range.mp hi]

@[simp] theorem toComplex_eval {n : ℕ} (p : QPoly n) (x : GaussianRat) :
    GaussianRat.toComplex (eval p x) = evalComplex p (GaussianRat.toComplex x) := by
  rw [evalComplex, eval, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [coeff, Finset.mem_range.mp hi]

@[simp] theorem evalComplex_add {n : ℕ} (p q : QPoly n) (x : ℂ) :
    evalComplex (add p q) x = evalComplex p x + evalComplex q x := by
  simp [evalComplex, Finset.sum_add_distrib, add_mul]

@[simp] theorem evalComplex_mul {n m : ℕ} (p : QPoly n) (q : QPoly m) (x : ℂ) :
    evalComplex (mul p q) x = evalComplex p x * evalComplex q x := by
  simp [evalComplex_eq_toComplexPolynomial_eval, toComplexPolynomial_eq_map]

@[simp] theorem evalComplex_translate {n : ℕ} (a : GaussianRat) (p : QPoly n) (x : ℂ) :
    evalComplex (translate a p) x =
      evalComplex p (x + GaussianRat.toComplex a) := by
  simp [evalComplex_eq_toComplexPolynomial_eval, toComplexPolynomial_eq_map,
    Polynomial.map_taylor, Polynomial.taylor_eval]

/-! ## Coefficient L1 data -/

/-- L1 norm of the `i`th coefficient, extended by zero beyond the bound. -/
def coeffL1 {n : ℕ} (p : QPoly n) (i : ℕ) : ℚ := GaussianRat.l1 (coeff p i)

/-- Sum of the exact rational L1 norms of all stored coefficients. -/
def coefficientL1Sum {n : ℕ} (p : QPoly n) : ℚ :=
  ∑ i : Fin (n + 1), GaussianRat.l1 (p i)

/-- Maximum of the stored coefficient L1 norms (the vector is nonempty). -/
def coefficientL1Max {n : ℕ} (p : QPoly n) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i : Fin (n + 1) => GaussianRat.l1 (p i))

theorem coeffL1_nonneg {n : ℕ} (p : QPoly n) (i : ℕ) : 0 ≤ coeffL1 p i :=
  GaussianRat.l1_nonneg _

theorem coefficientL1Sum_nonneg {n : ℕ} (p : QPoly n) : 0 ≤ coefficientL1Sum p := by
  exact Finset.sum_nonneg fun _ _ => GaussianRat.l1_nonneg _

theorem coefficientL1_le_sum {n : ℕ} (p : QPoly n) (i : Fin (n + 1)) :
    GaussianRat.l1 (p i) ≤ coefficientL1Sum p := by
  exact Finset.single_le_sum (fun j _ => GaussianRat.l1_nonneg (p j)) (Finset.mem_univ i)

theorem coefficientL1_le_max {n : ℕ} (p : QPoly n) (i : Fin (n + 1)) :
    GaussianRat.l1 (p i) ≤ coefficientL1Max p := by
  exact Finset.le_sup' (fun j : Fin (n + 1) => GaussianRat.l1 (p j)) (Finset.mem_univ i)

/-! ## Native-evaluation smoke tests

These commands exercise the executable definitions themselves.  In
particular, they fail to compile if degree, multiplication, or translation
accidentally acquires a dependency on a noncomputable polynomial operation.
-/

private def smokeQuadratic : QPoly2 := fun i =>
  if i = 0 then 1 else if i = 1 then 2 else 3

private def smokeLinear : QPoly1 := fun i =>
  if i = 0 then 1 else 1

#synth Encodable QPoly4
#eval degree smokeQuadratic
#eval ((mul smokeQuadratic smokeLinear) (3 : Fin 4)).re
#eval ((translate (1 : GaussianRat) smokeQuadratic) (0 : Fin 3)).re

example : degree smokeQuadratic = 2 := by native_decide
example : ((mul smokeQuadratic smokeLinear) (3 : Fin 4)).re = 3 := by native_decide
example : ((translate (1 : GaussianRat) smokeQuadratic) (0 : Fin 3)).re = 6 := by
  native_decide

end QPoly

end GaussianPolynomialApproximationCore

end LeanProofs.PolynomialFormulas
