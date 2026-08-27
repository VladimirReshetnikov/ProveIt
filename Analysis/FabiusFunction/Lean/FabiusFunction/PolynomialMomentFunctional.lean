import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Finite moment functionals on polynomials

This module isolates the algebra common to finite-difference, Prouhet, and
quadrature arguments.  Given finitely many weights `weight i` and nodes
`node i`, suppose their weighted monomial moments vanish in every degree
strictly below `n`.  On polynomials of degree at most `n`, the resulting
evaluation sum then sees only the coefficient of degree `n`: it is that
coefficient times the top moment.

The results hold over an arbitrary commutative semiring.  A scalar-extension
layer allows the polynomial coefficients to lie in a different semiring and
evaluates them through an arbitrary ring homomorphism.  All degree hypotheses
use `Polynomial.degree`, rather than `natDegree`, so the zero polynomial is
handled correctly even at `n = 0`.  Empty index sets and subsingleton semirings
require no separate cases.

## Main results

* `sum_weight_mul_eval_eq_coeff_mul_of_moments` -- extraction with a supplied
  exact top moment.
* `sum_weight_mul_eval₂_eq_map_coeff_mul_of_moments` -- the corresponding
  scalar-extension theorem for an arbitrary coefficient homomorphism.
* `sum_weight_mul_eval_eq_coeff_mul_top_moment` -- the same theorem with the
  top moment left in its defining finite-sum form.
* `sum_weight_mul_eval_eq_zero_of_degree_lt` -- strict-degree annihilation.
* `sum_weight_mul_eval_congr_of_coeff_eq` -- two degree-bounded polynomials
  with the same top coefficient have the same weighted evaluation sum.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

/-- **Finite moment coefficient extraction.**  Let `weight` and `node` be a
finite weighted node family whose monomial moments below `n` vanish and whose
moment in degree `n` is exactly `c`.  Then, on every polynomial of degree at
most `n`, its weighted evaluation sum is the coefficient of degree `n`
multiplied by `c`.

The degree-valued hypothesis includes all boundary cases uniformly.  In
particular, at `n = 0` it allows every constant polynomial (and the zero
polynomial), while the lower-moment hypothesis is vacuous. -/
theorem sum_weight_mul_eval_eq_coeff_mul_of_moments
    {R : Type*} [CommSemiring R] {ι : Type*}
    (s : Finset ι) (weight node : ι → R) (n : ℕ) (c : R)
    (hlower : ∀ d < n, ∑ i ∈ s, weight i * node i ^ d = 0)
    (htop : (∑ i ∈ s, weight i * node i ^ n) = c)
    (p : Polynomial R) (hp : p.degree ≤ (n : WithBot ℕ)) :
    (∑ i ∈ s, weight i * p.eval (node i)) = p.coeff n * c := by
  classical
  have hnat : p.natDegree ≤ n :=
    Polynomial.natDegree_le_of_degree_le hp
  simp_rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hfactor (d : ℕ) :
      (∑ i ∈ s, weight i * (p.coeff d * node i ^ d)) =
        p.coeff d * ∑ i ∈ s, weight i * node i ^ d := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ac_rfl
  simp_rw [hfactor]
  by_cases hn : n ∈ p.support
  · rw [Finset.sum_eq_single n]
    · rw [htop]
    · intro d hd hdn
      have hdn' : d < n :=
        lt_of_le_of_ne
          (Polynomial.le_natDegree_of_mem_supp d hd |>.trans hnat) hdn
      rw [hlower d hdn', mul_zero]
    · exact fun h => (h hn).elim
  · have hcoeff : p.coeff n = 0 := by
      simpa only [Polynomial.mem_support_iff, not_ne_iff] using hn
    rw [hcoeff, zero_mul]
    apply Finset.sum_eq_zero
    intro d hd
    have hdn : d ≠ n := fun h => hn (h ▸ hd)
    have hdn' : d < n :=
      lt_of_le_of_ne
        (Polynomial.le_natDegree_of_mem_supp d hd |>.trans hnat) hdn
    rw [hlower d hdn', mul_zero]

/-- **Finite moment extraction after scalar extension.**  Let the polynomial
coefficients lie in a semiring `R`, while the weights and nodes lie in a
commutative semiring `A`.  Evaluation through any ring homomorphism from `R`
to `A` extracts the image of the top coefficient.

This is strictly more general than the same-ring theorem: the coefficient map
need not be injective, and mapping may lower the polynomial degree. -/
theorem sum_weight_mul_eval₂_eq_map_coeff_mul_of_moments
    {R A : Type*} [Semiring R] [CommSemiring A] { ι : Type*}
    (f : R →+* A) (s : Finset ι) (weight node : ι → A) (n : ℕ) (c : A)
    (hlower : ∀ d < n, ∑ i ∈ s, weight i * node i ^ d = 0)
    (htop : (∑ i ∈ s, weight i * node i ^ n) = c)
    (p : Polynomial R) (hp : p.degree ≤ (n : WithBot ℕ)) :
    (∑ i ∈ s, weight i * p.eval₂ f (node i)) = f (p.coeff n) * c := by
  have hdegree : (p.map f).degree ≤ (n : WithBot ℕ) :=
    Polynomial.degree_map_le.trans hp
  simpa only [Polynomial.eval_map, Polynomial.coeff_map] using
    (sum_weight_mul_eval_eq_coeff_mul_of_moments
      s weight node n c hlower htop (p.map f) hdegree)

/-- Normalization-free scalar-extension form of finite moment coefficient
extraction.  The top moment remains in its defining finite-sum form. -/
theorem sum_weight_mul_eval₂_eq_map_coeff_mul_top_moment
    {R A : Type*} [Semiring R] [CommSemiring A] { ι : Type*}
    (f : R →+* A) (s : Finset ι) (weight node : ι → A) (n : ℕ)
    (hlower : ∀ d < n, ∑ i ∈ s, weight i * node i ^ d = 0)
    (p : Polynomial R) (hp : p.degree ≤ (n : WithBot ℕ)) :
    (∑ i ∈ s, weight i * p.eval₂ f (node i)) =
      f (p.coeff n) * ∑ i ∈ s, weight i * node i ^ n := by
  exact sum_weight_mul_eval₂_eq_map_coeff_mul_of_moments
    f s weight node n (∑ i ∈ s, weight i * node i ^ n)
      hlower rfl p hp

/-- **Strict-degree cancellation after scalar extension.**  The weighted node
family annihilates the image of every polynomial of degree strictly below
`n`, for an arbitrary coefficient homomorphism. -/
theorem sum_weight_mul_eval₂_eq_zero_of_degree_lt
    {R A : Type*} [Semiring R] [CommSemiring A] { ι : Type*}
    (f : R →+* A) (s : Finset ι) (weight node : ι → A) (n : ℕ)
    (hlower : ∀ d < n, ∑ i ∈ s, weight i * node i ^ d = 0)
    (p : Polynomial R) (hp : p.degree < (n : WithBot ℕ)) :
    (∑ i ∈ s, weight i * p.eval₂ f (node i)) = 0 := by
  rw [sum_weight_mul_eval₂_eq_map_coeff_mul_top_moment
      f s weight node n hlower p hp.le,
    Polynomial.coeff_eq_zero_of_degree_lt hp, map_zero, zero_mul]

/-- **Mapped top-coefficient congruence.**  Two degree-bounded polynomials
have equal weighted evaluation sums whenever the chosen coefficient
homomorphism identifies their coefficients of degree `n`. -/
theorem sum_weight_mul_eval₂_congr_of_map_coeff_eq
    {R A : Type*} [Semiring R] [CommSemiring A] { ι : Type*}
    (f : R →+* A) (s : Finset ι) (weight node : ι → A) (n : ℕ)
    (hlower : ∀ d < n, ∑ i ∈ s, weight i * node i ^ d = 0)
    (p q : Polynomial R)
    (hp : p.degree ≤ (n : WithBot ℕ))
    (hq : q.degree ≤ (n : WithBot ℕ))
    (hcoeff : f (p.coeff n) = f (q.coeff n)) :
    (∑ i ∈ s, weight i * p.eval₂ f (node i)) =
      ∑ i ∈ s, weight i * q.eval₂ f (node i) := by
  rw [sum_weight_mul_eval₂_eq_map_coeff_mul_top_moment
      f s weight node n hlower p hp,
    sum_weight_mul_eval₂_eq_map_coeff_mul_top_moment
      f s weight node n hlower q hq,
    hcoeff]

/-- Normalization-free form of finite moment coefficient extraction.  If all
moments below `n` vanish, then the functional on a polynomial of degree at
most `n` is its coefficient of degree `n` times the actual top moment. -/
theorem sum_weight_mul_eval_eq_coeff_mul_top_moment
    {R : Type*} [CommSemiring R] {ι : Type*}
    (s : Finset ι) (weight node : ι → R) (n : ℕ)
    (hlower : ∀ d < n, ∑ i ∈ s, weight i * node i ^ d = 0)
    (p : Polynomial R) (hp : p.degree ≤ (n : WithBot ℕ)) :
    (∑ i ∈ s, weight i * p.eval (node i)) =
      p.coeff n * ∑ i ∈ s, weight i * node i ^ n := by
  exact sum_weight_mul_eval_eq_coeff_mul_of_moments
    s weight node n (∑ i ∈ s, weight i * node i ^ n)
      hlower rfl p hp

/-- **Strict-degree finite moment cancellation.**  A weighted node family
whose moments below `n` vanish annihilates every polynomial of degree strictly
below `n`.  For `n = 0`, the degree hypothesis admits precisely the zero
polynomial in a nontrivial semiring, so the empty-boundary case is included. -/
theorem sum_weight_mul_eval_eq_zero_of_degree_lt
    {R : Type*} [CommSemiring R] {ι : Type*}
    (s : Finset ι) (weight node : ι → R) (n : ℕ)
    (hlower : ∀ d < n, ∑ i ∈ s, weight i * node i ^ d = 0)
    (p : Polynomial R) (hp : p.degree < (n : WithBot ℕ)) :
    (∑ i ∈ s, weight i * p.eval (node i)) = 0 := by
  rw [sum_weight_mul_eval_eq_coeff_mul_top_moment
      s weight node n hlower p hp.le,
    Polynomial.coeff_eq_zero_of_degree_lt hp, zero_mul]

/-- **Top-coefficient congruence.**  Under the lower-moment hypotheses, the
weighted evaluation functional has the same value on any two polynomials of
degree at most `n` whose coefficients of degree `n` agree. -/
theorem sum_weight_mul_eval_congr_of_coeff_eq
    {R : Type*} [CommSemiring R] {ι : Type*}
    (s : Finset ι) (weight node : ι → R) (n : ℕ)
    (hlower : ∀ d < n, ∑ i ∈ s, weight i * node i ^ d = 0)
    (p q : Polynomial R)
    (hp : p.degree ≤ (n : WithBot ℕ))
    (hq : q.degree ≤ (n : WithBot ℕ))
    (hcoeff : p.coeff n = q.coeff n) :
    (∑ i ∈ s, weight i * p.eval (node i)) =
      ∑ i ∈ s, weight i * q.eval (node i) := by
  rw [sum_weight_mul_eval_eq_coeff_mul_top_moment
      s weight node n hlower p hp,
    sum_weight_mul_eval_eq_coeff_mul_top_moment
      s weight node n hlower q hq,
    hcoeff]

end Fabius
