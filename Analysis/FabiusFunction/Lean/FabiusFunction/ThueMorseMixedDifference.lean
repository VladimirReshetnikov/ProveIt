import FabiusFunction.ThueMorseSparseMoments

/-!
# Finite mixed differences of commuting translations

This module develops the operator identity underlying the dyadic
Thue--Morse cancellation formula.  The primary construction is independent
of dyadic arithmetic.  Let an additive commutative monoid `V` act on a type
`P`, let `step : ι → V` be an arbitrary family of translation steps, and let
`s : Finset ι`.  For a function `f : P → A`, with values in an additive
commutative group, define

`mixedDifference step s f x = ∏_(i ∈ s) (I - T_(step i)) f(x)`.

Because `V` is commutative, its translations commute.  The operator is
therefore indexed by a finite set rather than an ordering of that set, and
has the inclusion--exclusion expansion

`mixedDifference step s f x =
  ∑_(t ⊆ s) (-1)^|t| • f((∑_(i ∈ t) step i) +ᵥ x)`.

The insert recurrence peels off one arbitrary translation.  It is the
reusable foundation for later sparse and `bitSupport` specializations.
Repeated step values are allowed: distinct indices still represent distinct
difference factors.

The former dyadic API is retained as the specialization
`step j = 2^j • h`, `s = range m`.  Its recurrence and powerset expansion are
now consequences of the general operator layer.  Finally, the classical
Thue--Morse block identity follows by identifying a subset of dyadic scales
with the integer having exactly those binary digits.

## Main results

* `mixedDifference` -- the arbitrary finite family of commuting translation
  differences.
* `mixedDifference_insert` -- the recurrence
  `Δ_(insert i s) f x = Δ_s f x - Δ_s f (step i +ᵥ x)`.
* `mixedDifference_eq_sum_powerset_smul` -- its full powerset expansion.
* `dyadicMixedDifference` -- the compatibility specialization at the dyadic
  steps `2^j • h`.
* `sum_thueMorseSign_smul_eq_mixedDifference` -- the dyadic Thue--Morse
  block sum as that specialization of the mixed-difference operator.

No algebraic structure is imposed on the test function.  The point type need
not itself be additive: an action of the step monoid is enough.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- The mixed-difference operator attached to a finite family of commuting
additive translations.  It is defined by its order-free
inclusion--exclusion expansion over the powerset of the index set. -/
def mixedDifference {V P A ι : Type*} [AddCommMonoid V] [AddAction V P]
    [AddCommGroup A] (step : ι → V) (s : Finset ι) (f : P → A) (x : P) : A :=
  ∑ t ∈ s.powerset,
    ((-1 : ℤ) ^ t.card) • f ((∑ i ∈ t, step i) +ᵥ x)

/-- Inclusion--exclusion expansion of a finite mixed difference.  This
theorem exposes the defining formula without requiring clients to unfold the
operator. -/
theorem mixedDifference_eq_sum_powerset_smul
    {V P A ι : Type*} [AddCommMonoid V] [AddAction V P] [AddCommGroup A]
    (step : ι → V) (s : Finset ι) (f : P → A) (x : P) :
    mixedDifference step s f x =
      ∑ t ∈ s.powerset,
        ((-1 : ℤ) ^ t.card) • f ((∑ i ∈ t, step i) +ᵥ x) :=
  rfl

/-- The empty family of translations acts as the identity operator. -/
@[simp] theorem mixedDifference_empty
    {V P A ι : Type*} [AddCommMonoid V] [AddAction V P] [AddCommGroup A]
    (step : ι → V) (f : P → A) (x : P) :
    mixedDifference step ∅ f x = f x := by
  simp [mixedDifference]

/-- Peeling one translation from a finite mixed difference.  The hypothesis
`i ∉ s` records that the new index contributes a genuinely new difference
factor; its step value may coincide with another step value. -/
theorem mixedDifference_insert
    {V P A ι : Type*} [AddCommMonoid V] [AddAction V P] [AddCommGroup A]
    [DecidableEq ι]
    (step : ι → V) (s : Finset ι) (f : P → A) (x : P) {i : ι}
    (hi : i ∉ s) :
    mixedDifference step (insert i s) f x =
      mixedDifference step s f x -
        mixedDifference step s f (step i +ᵥ x) := by
  classical
  unfold mixedDifference
  rw [Finset.sum_powerset_insert hi, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun t ht ↦ ?_
  have hit : i ∉ t :=
    Finset.notMem_of_mem_powerset_of_notMem ht hi
  have hpoint :
      (step i + ∑ j ∈ t, step j) +ᵥ x =
        (∑ j ∈ t, step j) +ᵥ (step i +ᵥ x) := by
    calc
      (step i + ∑ j ∈ t, step j) +ᵥ x =
          ((∑ j ∈ t, step j) + step i) +ᵥ x := by rw [add_comm]
      _ = (∑ j ∈ t, step j) +ᵥ (step i +ᵥ x) :=
        add_vadd _ _ _
  rw [Finset.card_insert_of_notMem hit, Finset.sum_insert hit,
    pow_succ, mul_neg, mul_one, neg_smul, hpoint]

/-- A one-step mixed difference is the ordinary translation difference
`f(x) - f(step i +ᵥ x)`. -/
@[simp] theorem mixedDifference_singleton
    {V P A ι : Type*} [AddCommMonoid V] [AddAction V P] [AddCommGroup A]
    (step : ι → V) (i : ι) (f : P → A) (x : P) :
    mixedDifference step {i} f x = f x - f (step i +ᵥ x) := by
  classical
  simpa using
    (mixedDifference_insert (step := step) (s := (∅ : Finset ι))
      (f := f) (x := x) (i := i) (hi := by simp))

/-! ## Dyadic specialization -/

/-- The dyadic mixed-difference operator `∏_(j<m) (I - T_(2^j h))`, now
defined as the specialization of `mixedDifference` to `range m`. -/
def dyadicMixedDifference {M A : Type*} [AddCommMonoid M] [AddCommGroup A]
    (h : M) (m : ℕ) (f : M → A) (x : M) : A :=
  mixedDifference (fun j : ℕ ↦ 2 ^ j • h) (range m) f x

@[simp] theorem dyadicMixedDifference_zero {M A : Type*} [AddCommMonoid M]
    [AddCommGroup A] (h : M) (f : M → A) (x : M) :
    dyadicMixedDifference h 0 f x = f x := by
  simp [dyadicMixedDifference]

/-- Peeling the top dyadic scale, retained in the original API form. -/
theorem dyadicMixedDifference_succ {M A : Type*} [AddCommMonoid M]
    [AddCommGroup A] (h : M) (m : ℕ) (f : M → A) (x : M) :
    dyadicMixedDifference h (m + 1) f x =
      dyadicMixedDifference h m f x -
        dyadicMixedDifference h m f (x + 2 ^ m • h) := by
  unfold dyadicMixedDifference
  rw [Finset.range_add_one, mixedDifference_insert (hi := by simp)]
  simp only [vadd_eq_add]
  rw [add_comm (2 ^ m • h) x]

/-- Powerset expansion of the dyadic mixed difference in the original
right-translation notation. -/
theorem dyadicMixedDifference_eq_sum_powerset_smul
    {M A : Type*} [AddCommMonoid M] [AddCommGroup A]
    (h : M) (m : ℕ) (f : M → A) (x : M) :
    dyadicMixedDifference h m f x =
      ∑ t ∈ (range m).powerset,
        ((-1 : ℤ) ^ t.card) •
          f (x + (∑ j ∈ t, 2 ^ j) • h) := by
  unfold dyadicMixedDifference mixedDifference
  refine Finset.sum_congr rfl fun t _ht ↦ ?_
  rw [Finset.sum_nsmul_assoc, vadd_eq_add, add_comm]

/-- The expanded dyadic inclusion--exclusion form: the signed block sum is
the alternating sum over the Boolean cube of scales,
`∑_(t⊆{0,…,m-1}) (-1)^|t| • f(x + (∑_(j∈t) 2^j)•h)`. -/
theorem sum_thueMorseSign_smul_eq_sum_powerset_smul {M A : Type*}
    [AddCommMonoid M] [AddCommGroup A] (h : M) (f : M → A) (m : ℕ) (x : M) :
    ∑ n ∈ range (2 ^ m), thueMorseSign n • f (x + n • h) =
      ∑ t ∈ (range m).powerset,
        ((-1 : ℤ) ^ t.card) • f (x + (∑ j ∈ t, 2 ^ j) • h) := by
  rw [← sum_powerset_two_pow m
    (fun n ↦ thueMorseSign n • f (x + n • h))]
  refine Finset.sum_congr rfl fun t _ht ↦ ?_
  rw [thueMorseSign_sum_two_pow]

/-- **Dyadic finite-difference factorization.**  For every function from an
additive commutative monoid into an additive commutative group,
`∑_(n<2^m) ε(n) • f(x + n•h) = (∏_(j<m) (I - T_(2^j h)) f)(x)`.
This is now a thin consequence of the dyadic powerset parametrization and
the arbitrary-step mixed-difference expansion. -/
theorem sum_thueMorseSign_smul_eq_mixedDifference {M A : Type*}
    [AddCommMonoid M] [AddCommGroup A] (h : M) (f : M → A) (m : ℕ) (x : M) :
    ∑ n ∈ range (2 ^ m), thueMorseSign n • f (x + n • h) =
      dyadicMixedDifference h m f x := by
  calc
    ∑ n ∈ range (2 ^ m), thueMorseSign n • f (x + n • h) =
        ∑ t ∈ (range m).powerset,
          ((-1 : ℤ) ^ t.card) • f (x + (∑ j ∈ t, 2 ^ j) • h) :=
      sum_thueMorseSign_smul_eq_sum_powerset_smul h f m x
    _ = dyadicMixedDifference h m f x :=
      (dyadicMixedDifference_eq_sum_powerset_smul h m f x).symm

end Fabius
