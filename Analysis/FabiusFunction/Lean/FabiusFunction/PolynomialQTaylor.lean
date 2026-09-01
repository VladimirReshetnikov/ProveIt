import FabiusFunction.PolynomialQLeibniz
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# q-falling powers and the q-Taylor formula

The `q`-falling power based at `a` is the polynomial

`(x - a)^{⟨m⟩}_q = ∏_{j<m} (x - q^j a)`,

monic of degree `m`, vanishing at `a` for `m ≥ 1`.  Its `q`-derivative is

`D_q (x - a)^{⟨m+1⟩}_q = [m+1]_q (x - a)^{⟨m⟩}_q`,

proved by induction from the product rule and `[m+2]_q = 1 + q [m+1]_q`; hence

`D_q^j (x - a)^{⟨m⟩}_q = [m]_q [m-1]_q ⋯ [m-j+1]_q · (x - a)^{⟨m-j⟩}_q`

for *every* `j` (for `j > m` the falling factorial contains `[0]_q = 0`).

The **`q`-Taylor formula** follows: over a field with `[j]_q ≠ 0` for
`1 ≤ j ≤ N`, every polynomial `f` of degree at most `N` satisfies

`f = ∑_{k=0}^{N} (D_q^k f)(a) / [k]_q! · (x - a)^{⟨k⟩}_q`.

The proof peels off the leading falling power: `f - c (x-a)^{⟨N+1⟩}_q` has
degree at most `N` for `c` the coefficient of `x^{N+1}`, the induction
hypothesis applies to it, and the `q`-derivatives of the peeled term
contribute nothing at `a` except at order `N+1`, where they contribute
exactly `c [N+1]_q!`.  When the nodes `a, qa, q^2 a, …` are distinct this is
Newton interpolation on the geometric grid.

## Main declarations

* `qFallingPower`, `qFallingPower_monic`, `qFallingPower_natDegree`,
  `qFallingPower_eval_self`.
* `qDerivative_qFallingPower_succ`, `qDerivative_iterate_qFallingPower`.
* `qDerivative_iterate_C_mul_X_pow`, `qDerivative_iterate_eq_zero_of_natDegree_le`.
* `qFactorial`: `[n]_q! = ∏_{i<n} [i+1]_q`.
* `qTaylor`: the `q`-Taylor formula.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Polynomial Finset

section Semiring

variable {R : Type*} [CommSemiring R]

/-- The `q`-factorial `[n]_q! = [1]_q [2]_q ⋯ [n]_q`. -/
def qFactorial (q : R) (n : ℕ) : R := ∏ i ∈ range n, qInt q (i + 1)

/-- The zeroth `q`-factorial is one. -/
@[simp] theorem qFactorial_zero (q : R) : qFactorial q 0 = 1 := by simp [qFactorial]

/-- Recurrence `[n+1]_q! = [n]_q! [n+1]_q`. -/
theorem qFactorial_succ (q : R) (n : ℕ) : qFactorial q (n + 1) = qFactorial q n * qInt q (n + 1) := by
  simp [qFactorial, Finset.prod_range_succ]

/-- The `q`-derivative of the constant polynomial one is zero. -/
@[simp] theorem qDerivative_one (q : R) : qDerivative q (1 : R[X]) = 0 := by
  simpa using qDerivative_C q 1

/-- Iterates of `D_q` are additive. -/
theorem qDerivative_iterate_add (q : R) (k : ℕ) (f g : R[X]) :
    (qDerivative q)^[k] (f + g) = (qDerivative q)^[k] f + (qDerivative q)^[k] g := by
  induction k generalizing f g with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply, map_add, ih]

/-- Iterates of `D_q` commute with constants. -/
theorem qDerivative_iterate_C_mul (q c : R) (k : ℕ) (f : R[X]) :
    (qDerivative q)^[k] (C c * f) = C c * (qDerivative q)^[k] f := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply, qDerivative_C_mul, ih]

/-- Iterates of `D_q` are additive over finite sums. -/
theorem qDerivative_iterate_sum {ι : Type*} (q : R) (k : ℕ) (s : Finset ι) (f : ι → R[X]) :
    (qDerivative q)^[k] (∑ i ∈ s, f i) = ∑ i ∈ s, (qDerivative q)^[k] (f i) := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply, map_sum, ih]

/-- `D_q^k (a X^n) = a [n]_q [n-1]_q ⋯ [n-k+1]_q X^{n-k}`, for every `k`. -/
theorem qDerivative_iterate_C_mul_X_pow (q a : R) (n k : ℕ) :
    (qDerivative q)^[k] (C a * X ^ n) =
      C (a * ∏ i ∈ range k, qInt q (n - i)) * X ^ (n - k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, qDerivative_C_mul_X_pow, Finset.prod_range_succ,
        Nat.sub_sub, mul_assoc]

/-- A polynomial of degree at most `n` is annihilated by `D_q^{n+1}`. -/
theorem qDerivative_iterate_eq_zero_of_natDegree_le (q : R) {p : R[X]} {n : ℕ}
    (hp : p.natDegree ≤ n) : (qDerivative q)^[n + 1] p = 0 := by
  rw [p.as_sum_range' (n + 1) (Nat.lt_succ_of_le hp), qDerivative_iterate_sum]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [← C_mul_X_pow_eq_monomial, qDerivative_iterate_C_mul_X_pow,
    Finset.prod_eq_zero (Finset.mem_range.mpr (Finset.mem_range.mp hi)) (by simp), mul_zero,
    map_zero, zero_mul]

end Semiring

section Ring

variable {R : Type*} [CommRing R]

/-- The `q`-falling power `(X - a)^{⟨m⟩}_q = ∏_{j<m} (X - q^j a)`. -/
noncomputable def qFallingPower (a q : R) (m : ℕ) : R[X] :=
  ∏ j ∈ range m, (X - C (q ^ j * a))

/-- The zeroth `q`-falling power is one. -/
@[simp] theorem qFallingPower_zero (a q : R) : qFallingPower a q 0 = 1 := by
  simp [qFallingPower]

/-- Append the factor `X - q^m a` to a `q`-falling power of length `m`. -/
theorem qFallingPower_succ (a q : R) (m : ℕ) :
    qFallingPower a q (m + 1) = qFallingPower a q m * (X - C (q ^ m * a)) := by
  simp [qFallingPower, Finset.prod_range_succ]

/-- Peeling the first factor: `(X - a)^{⟨m+1⟩}_q = (X - a) (X - qa)^{⟨m⟩}_q`. -/
theorem qFallingPower_succ' (a q : R) (m : ℕ) :
    qFallingPower a q (m + 1) = (X - C a) * qFallingPower (q * a) q m := by
  rw [qFallingPower, Finset.prod_range_succ', pow_zero, one_mul, mul_comm, qFallingPower]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [pow_succ, mul_assoc]

/-- Every `q`-falling power is monic. -/
theorem qFallingPower_monic (a q : R) (m : ℕ) : (qFallingPower a q m).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

/-- Over a nontrivial coefficient ring, a `q`-falling power of length `m`
has natural degree `m`. -/
theorem qFallingPower_natDegree [Nontrivial R] (a q : R) (m : ℕ) :
    (qFallingPower a q m).natDegree = m := by
  rw [qFallingPower, natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

/-- `(X - a)^{⟨m+1⟩}_q` vanishes at `a`. -/
theorem qFallingPower_eval_self (a q : R) (m : ℕ) :
    (qFallingPower a q (m + 1)).eval a = 0 := by
  rw [qFallingPower, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.succ_pos m)) (by simp)

/-- **The `q`-derivative of a falling power**:
`D_q (X - a)^{⟨m+1⟩}_q = [m+1]_q (X - a)^{⟨m⟩}_q`. -/
theorem qDerivative_qFallingPower_succ (a q : R) (m : ℕ) :
    qDerivative q (qFallingPower a q (m + 1)) = C (qInt q (m + 1)) * qFallingPower a q m := by
  induction m with
  | zero =>
      rw [qFallingPower_succ, qFallingPower_zero, one_mul, map_sub, qDerivative_X, qDerivative_C,
        sub_zero, qInt_one, C_1, one_mul]
  | succ m ih =>
      rw [qFallingPower_succ a q (m + 1), qDerivative_mul', ih, map_sub, qDerivative_X,
        qDerivative_C, sub_zero, sub_comp, X_comp, C_comp, qInt_succ' q (m + 1),
        qFallingPower_succ a q m, pow_succ']
      simp only [C_add, C_mul, C_1, C_pow]
      ring

/-- **Iterated `q`-derivatives of a falling power**, for every `j`:
`D_q^j (X - a)^{⟨m⟩}_q = [m]_q [m-1]_q ⋯ [m-j+1]_q · (X - a)^{⟨m-j⟩}_q`. -/
theorem qDerivative_iterate_qFallingPower (a q : R) (m j : ℕ) :
    (qDerivative q)^[j] (qFallingPower a q m) =
      C (∏ i ∈ range j, qInt q (m - i)) * qFallingPower a q (m - j) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih, qDerivative_C_mul, Finset.prod_range_succ, C_mul,
        mul_assoc]
      congr 1
      rcases Nat.lt_or_ge j m with hlt | hge
      · obtain ⟨k, hk⟩ : ∃ k, m - j = k + 1 := ⟨m - j - 1, by omega⟩
        rw [hk, qDerivative_qFallingPower_succ, show m - (j + 1) = k by omega]
      · rw [Nat.sub_eq_zero_of_le hge, Nat.sub_eq_zero_of_le (by omega : m ≤ j + 1), qInt_zero,
          map_zero, zero_mul, qFallingPower_zero, qDerivative_one]

end Ring

section Field

variable {K : Type*} [Field K]

/-- The falling `q`-factorial `[N+1]_q [N]_q ⋯ [1]_q` is `[N+1]_q!`. -/
theorem prod_qInt_sub_eq_qFactorial (q : K) (N : ℕ) :
    ∏ i ∈ range (N + 1), qInt q (N + 1 - i) = qFactorial q (N + 1) := by
  rw [qFactorial, ← Finset.prod_range_reflect]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' : i < N + 1 := Finset.mem_range.mp hi
  congr 1
  omega

/-- **The `q`-Taylor formula.**  If `[j]_q ≠ 0` for `1 ≤ j ≤ N`, every polynomial
`f` of degree at most `N` is
`f = ∑_{k=0}^{N} (D_q^k f)(a) / [k]_q! · (X - a)^{⟨k⟩}_q`. -/
theorem qTaylor {q : K} {N : ℕ} (hq : ∀ j, 1 ≤ j → j ≤ N → qInt q j ≠ 0) (a : K)
    (f : K[X]) (hf : f.natDegree ≤ N) :
    f = ∑ k ∈ range (N + 1),
      C (((qDerivative q)^[k] f).eval a / qFactorial q k) * qFallingPower a q k := by
  induction N generalizing f with
  | zero =>
      rw [eq_C_of_natDegree_le_zero hf]
      simp
  | succ N ih =>
      set c := f.coeff (N + 1) with hc
      set g := f - C c * qFallingPower a q (N + 1) with hg_def
      have hfg : f = g + C c * qFallingPower a q (N + 1) := (sub_add_cancel _ _).symm
      have hg : g.natDegree ≤ N := by
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro m hm
        rw [hg_def, coeff_sub, coeff_C_mul]
        rcases Nat.lt_or_ge (N + 1) m with h | h
        · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hf h),
            coeff_eq_zero_of_natDegree_lt (by rw [qFallingPower_natDegree]; exact h), mul_zero,
            sub_zero]
        · have hm' : m = N + 1 := by omega
          subst hm'
          have h1 := (qFallingPower_monic a q (N + 1)).coeff_natDegree
          rw [qFallingPower_natDegree] at h1
          rw [h1, mul_one, hc, sub_self]
      have hgzero : (qDerivative q)^[N + 1] g = 0 :=
        qDerivative_iterate_eq_zero_of_natDegree_le q hg
      have hfact : qFactorial q (N + 1) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun i hi =>
          hq (i + 1) (by omega) (Nat.succ_le_of_lt (Finset.mem_range.mp hi))
      have hsplit : ∀ k ∈ range (N + 1),
          C (((qDerivative q)^[k] f).eval a / qFactorial q k) * qFallingPower a q k =
            C (((qDerivative q)^[k] g).eval a / qFactorial q k) * qFallingPower a q k := by
        intro k hk
        have hkN : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [hfg, qDerivative_iterate_add, qDerivative_iterate_C_mul,
          qDerivative_iterate_qFallingPower, eval_add, eval_mul, eval_C, eval_mul, eval_C,
          show N + 1 - k = N - k + 1 by omega, qFallingPower_eval_self, mul_zero, mul_zero,
          add_zero]
      have hlast : C (((qDerivative q)^[N + 1] f).eval a / qFactorial q (N + 1)) *
          qFallingPower a q (N + 1) = C c * qFallingPower a q (N + 1) := by
        rw [hfg, qDerivative_iterate_add, qDerivative_iterate_C_mul, hgzero, zero_add,
          qDerivative_iterate_qFallingPower, Nat.sub_self, qFallingPower_zero, mul_one, eval_mul,
          eval_C, eval_C, prod_qInt_sub_eq_qFactorial, mul_div_cancel_right₀ _ hfact]
      rw [Finset.sum_range_succ, Finset.sum_congr rfl hsplit, hlast,
        ← ih (fun j h1 h2 => hq j h1 (by omega)) g hg]
      exact hfg

end Field

end Fabius
