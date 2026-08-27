import FabiusFunction.ThueMorseSparseMoments

/-!
# The dyadic mixed-difference master identity

The atlas's operator form of Prouhet cancellation: for an arbitrary test
function, `∑_{n<2^m} ε(n)·f(x + nh) = ∏_{j<m} (I - T_(2^j h)) f(x)` — an
inclusion–exclusion identity strictly stronger than any single moment
statement.  This module proves it in full generality: the argument space
is any additive commutative monoid, the value space any additive
commutative group, and no structure at all is assumed on `f`.

* `dyadicMixedDifference` — the operator `∏_{j<m} (I - T_(2^j h))`,
  defined by peeling the top scale.
* `sum_thueMorseSign_smul_eq_mixedDifference` — the boxed identity
  `∑_{n<2^m} ε(n) • f(x + n•h) = (∏_{j<m} (I - T_(2^j h)) f)(x)`,
  by induction on the block level through the reflection
  `ε(2^m + n) = -ε(n)`.
* `sum_thueMorseSign_smul_eq_sum_powerset_smul` — the expanded
  inclusion–exclusion form over the Boolean cube of scales.

Specializing the value group to a commutative ring and `f` to a
polynomial recovers the Prouhet annihilation results of
`ThueMorseSparseProuhet`; specializing `f` to `exp` recovers the moment
generating identities of `ThueMorseMoments`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- The dyadic mixed-difference operator `∏_{j<m} (I - T_(2^j h))`:
`m+1` scales peel the top factor `I - T_(2^m h)`. -/
def dyadicMixedDifference {M A : Type*} [AddCommMonoid M] [AddCommGroup A]
    (h : M) : ℕ → (M → A) → M → A
  | 0, f, x => f x
  | m + 1, f, x =>
      dyadicMixedDifference h m f x -
        dyadicMixedDifference h m f (x + 2 ^ m • h)

@[simp] theorem dyadicMixedDifference_zero {M A : Type*} [AddCommMonoid M]
    [AddCommGroup A] (h : M) (f : M → A) (x : M) :
    dyadicMixedDifference h 0 f x = f x := rfl

theorem dyadicMixedDifference_succ {M A : Type*} [AddCommMonoid M]
    [AddCommGroup A] (h : M) (m : ℕ) (f : M → A) (x : M) :
    dyadicMixedDifference h (m + 1) f x =
      dyadicMixedDifference h m f x -
        dyadicMixedDifference h m f (x + 2 ^ m • h) := rfl

/-- **Dyadic finite-difference factorization.**  For every function from
an additive commutative monoid into an additive commutative group,
`∑_{n<2^m} ε(n) • f(x + n•h) = (∏_{j<m} (I - T_(2^j h)) f)(x)`:
Prouhet cancellation as an operator identity for arbitrary test
functions. -/
theorem sum_thueMorseSign_smul_eq_mixedDifference {M A : Type*}
    [AddCommMonoid M] [AddCommGroup A] (h : M) (f : M → A) (m : ℕ) (x : M) :
    ∑ n ∈ range (2 ^ m), thueMorseSign n • f (x + n • h) =
      dyadicMixedDifference h m f x := by
  induction m generalizing x with
  | zero =>
      simp [thueMorseSign, binaryWeight]
  | succ m ih =>
      rw [dyadicMixedDifference_succ, ← ih x, ← ih (x + 2 ^ m • h),
        show 2 ^ (m + 1) = 2 ^ m + 2 ^ m by rw [pow_succ]; omega,
        Finset.sum_range_add, sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      refine Finset.sum_congr rfl fun n hn => ?_
      have hnlt := Finset.mem_range.mp hn
      rw [thueMorseSign_add_pow_two m n hnlt, neg_smul, neg_inj, add_smul]
      congr 1
      rw [add_assoc]

/-- The expanded inclusion–exclusion form: the signed block sum equals the
alternating sum over the Boolean cube of scales,
`∑_{T⊆{0,…,m-1}} (-1)^|T| • f(x + (∑_{j∈T} 2^j)•h)`. -/
theorem sum_thueMorseSign_smul_eq_sum_powerset_smul {M A : Type*}
    [AddCommMonoid M] [AddCommGroup A] (h : M) (f : M → A) (m : ℕ) (x : M) :
    ∑ n ∈ range (2 ^ m), thueMorseSign n • f (x + n • h) =
      ∑ T ∈ (range m).powerset,
        ((-1 : ℤ) ^ T.card) • f (x + (∑ j ∈ T, 2 ^ j) • h) := by
  rw [← sum_powerset_two_pow m (fun n => thueMorseSign n • f (x + n • h))]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [thueMorseSign_sum_two_pow]

end Fabius
