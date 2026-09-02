import FabiusFunction.FiniteQBinomialCore
import FabiusFunction.QPartialFractions
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# q-multinomial coefficients

The `q`-multinomial coefficient of a composition `n = n₁ + ⋯ + n_r` is defined
here, in every commutative semiring, as the product of Gaussian coefficients

`[n; n₁,…,n_r]_q = ∏_{j=1}^{r-1} [N_j, n_j]_q`,  `N_j = n_j + ⋯ + n_r`,

read off the list `[n₁, …, n_r]` from the left.  The factorial form

`(q;q)_n = [n; n₁,…,n_r]_q · (q;q)_{n₁} ⋯ (q;q)_{n_r}`

then holds in every commutative ring, division-free, by induction on the
list from the cleared Gaussian identity `(q;q)_k [n,k]_q = (q^{n-k+1};q)_k`;
over a field with `(q;q)_n ≠ 0` it is the usual quotient.  Naturality in the
base gives polynomiality and positivity: `[n; n₁,…,n_r]_q` is the value at `q`
of a universal polynomial in `ℕ[X]`.

## Main declarations

* `qMultinomial`: the coefficient, as a product of Gaussian coefficients.
* `finiteQPochhammerIn_self_sum_eq_qMultinomial_mul`: the factorial form.
* `qMultinomial_eq_div`: the quotient form over a field.
* `map_qMultinomial`, `qMultinomial_eq_eval₂_universal`: naturality and
  polynomiality with natural coefficients.
* `qMultinomial_pair`: two parts give the Gaussian coefficient.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

section Semiring

variable {R : Type*} [Semiring R]

/-- The `q`-multinomial coefficient `[n; n₁,…,n_r]_q = ∏_j [n_j + ⋯ + n_r, n_j]_q` of the
composition given by a list, as a product of Gaussian coefficients. -/
def qMultinomial (q : R) : List ℕ → R
  | [] => 1
  | n :: l => gaussianBinomial q (n + l.sum) n * qMultinomial q l

/-- The q-multinomial coefficient of the empty composition is one. -/
@[simp] theorem qMultinomial_nil (q : R) : qMultinomial q [] = 1 := rfl

/-- Peeling the first part exposes one Gaussian coefficient and the
q-multinomial coefficient of the remaining composition. -/
theorem qMultinomial_cons (q : R) (n : ℕ) (l : List ℕ) :
    qMultinomial q (n :: l) = gaussianBinomial q (n + l.sum) n * qMultinomial q l := rfl

end Semiring

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- The diagonal Gaussian coefficient is one. -/
theorem gaussianBinomial_diag (q : R) (n : ℕ) : gaussianBinomial q n n = 1 := by
  rw [← gaussianBinomial_symm q le_rfl, Nat.sub_self, gaussianBinomial_zero_right]

/-- A one-part q-multinomial coefficient is one. -/
@[simp] theorem qMultinomial_singleton (q : R) (n : ℕ) : qMultinomial q [n] = 1 := by
  simp [qMultinomial_cons]

/-- Two parts give the Gaussian coefficient: `[n; k, n-k]_q = [n,k]_q`. -/
theorem qMultinomial_pair (q : R) {n k : ℕ} (hk : k ≤ n) :
    qMultinomial q [k, n - k] = gaussianBinomial q n k := by
  simp [qMultinomial_cons, Nat.add_sub_of_le hk]

/-- **Naturality**: ring homomorphisms commute with the `q`-multinomial coefficient. -/
theorem map_qMultinomial {S : Type*} [CommSemiring S] (φ : R →+* S) (q : R) (l : List ℕ) :
    φ (qMultinomial q l) = qMultinomial (φ q) l := by
  induction l with
  | nil => simp
  | cons n l ih => rw [qMultinomial_cons, qMultinomial_cons, map_mul, map_gaussianBinomial, ih]

/-- **Polynomiality and positivity**: `[n; n₁,…,n_r]_q` is the value at `q` of the
universal polynomial `[n; n₁,…,n_r]_X ∈ ℕ[X]`. -/
theorem qMultinomial_eq_eval₂_universal (q : R) (l : List ℕ) :
    qMultinomial q l =
      (qMultinomial (Polynomial.X : Polynomial ℕ) l).eval₂ (Nat.castRingHom R) q := by
  have h := map_qMultinomial (Polynomial.eval₂RingHom (Nat.castRingHom R) q) (Polynomial.X : Polynomial ℕ) l
  rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] at h
  exact h.symm

end CommSemiring

section Ring

variable {R : Type*} [CommRing R]

/-- **The factorial form**, division-free, in every commutative ring:
`(q;q)_{n₁+⋯+n_r} = [n; n₁,…,n_r]_q · (q;q)_{n₁} ⋯ (q;q)_{n_r}`. -/
theorem finiteQPochhammerIn_self_sum_eq_qMultinomial_mul (q : R) (l : List ℕ) :
    finiteQPochhammerIn q q l.sum =
      qMultinomial q l * (l.map fun n => finiteQPochhammerIn q q n).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have h1 := finiteQPochhammerIn_self_mul_gaussianBinomial q (Nat.le_add_left a l.sum)
      rw [Nat.add_sub_cancel, pow_succ'] at h1
      rw [List.sum_cons, List.map_cons, List.prod_cons, qMultinomial_cons, add_comm a l.sum,
        finiteQPochhammerIn_add, ← h1, ih]
      ring

end Ring

section Field

variable {K : Type*} [Field K]

/-- **The quotient form** over a field: for `(q;q)_n ≠ 0`,
`[n; n₁,…,n_r]_q = (q;q)_n / ((q;q)_{n₁} ⋯ (q;q)_{n_r})`. -/
theorem qMultinomial_eq_div (q : K) (l : List ℕ) (hq : finiteQPochhammerIn q q l.sum ≠ 0) :
    qMultinomial q l =
      finiteQPochhammerIn q q l.sum / (l.map fun n => finiteQPochhammerIn q q n).prod := by
  have hprod : (l.map fun n => finiteQPochhammerIn q q n).prod ≠ 0 := by
    intro h0
    obtain ⟨n, hn, h⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp h0)
    exact finiteQPochhammerIn_self_ne_zero_of_le hq (List.le_sum_of_mem hn) h
  rw [eq_div_iff hprod, finiteQPochhammerIn_self_sum_eq_qMultinomial_mul]

end Field

end Fabius
