import FabiusFunction.ThueMorseMixedDifference

/-!
# Symmetric mixed differences and centered Thue--Morse blocks

The arbitrary translation operator in `ThueMorseMixedDifference` has a
particularly clean centered form.  Give each index `i` a *half-step* `a i`.
The corresponding symmetric factor sends a function `f` to

`f (a i +ᵥ x) - f ((-a i) +ᵥ x)`.

For a finite set `s`, all these factors commute.  We package their product as
`symmetricMixedDifference a s f x`.  It is deliberately defined as one
ordinary mixed difference: start at the upper corner
`(∑ i ∈ s, a i) +ᵥ x` and use the full steps `-(2 • a i)`.  Consequently
all of the order-free operator machinery is inherited rather than reproved.

The powerset expansion evaluates `f` at the symmetric Boolean cube

`(∑ i ∈ s, a i) - 2 • (∑ i ∈ t, a i) +ᵥ x`,  `t ⊆ s`.

Over a commutative ring, a polynomial of degree below `|s|` is annihilated.
At degree `|s|` the two signs in the ordinary mixed-difference formula cancel,
leaving the sign-free sharp factor

`|s|! · ∏ i ∈ s, (2 • a i)`.

The final section takes the half-steps `2^j • h`.  Its Boolean-cube corners
are parametrized by a Thue--Morse block, giving a centered form of the Prouhet
identity without any new binary arithmetic.

## Main results

* `symmetricMixedDifference_insert` -- the centered recurrence obtained by
  peeling off one half-step;
* `symmetricMixedDifference_eq_sum_powerset_smul` -- the exact symmetric-cube
  expansion;
* `symmetricMixedDifference_polynomial_eq_coeff_card` -- sharp polynomial
  coefficient extraction with sign-free leading factor;
* `symmetricMixedDifference_polynomial_of_degree_lt` -- cancellation below
  the number of active half-steps, including the zero-polynomial boundary;
* `symmetricDyadicMixedDifference_eq_sum_thueMorseSign_smul` -- the centered
  dyadic operator as a signed Thue--Morse block sum;
* `symmetricDyadicMixedDifference_inv_two_pow_eq_sum_thueMorseSign_smul` --
  the same block on the increasing affine grid used by the continuous-chaos
  report.
-/

set_option autoImplicit false

open Finset Polynomial

namespace Fabius

/-- The product of centered translation differences with half-steps `a i`.
It is the ordinary mixed difference with full steps `-(2 • a i)`, based at
the upper corner `(∑ i ∈ s, a i) +ᵥ x` of the symmetric cube. -/
def symmetricMixedDifference {V P A ι : Type*} [AddCommGroup V]
    [AddAction V P] [AddCommGroup A] (a : ι → V) (s : Finset ι)
    (f : P → A) (x : P) : A :=
  mixedDifference (fun i ↦ -(2 • a i)) s f ((∑ i ∈ s, a i) +ᵥ x)

/-- With no active half-steps, the symmetric mixed difference is evaluation
at the center. -/
@[simp] theorem symmetricMixedDifference_empty
    {V P A ι : Type*} [AddCommGroup V] [AddAction V P] [AddCommGroup A]
    (a : ι → V) (f : P → A) (x : P) :
    symmetricMixedDifference a ∅ f x = f x := by
  simp [symmetricMixedDifference]

/-- One symmetric factor is the difference between the two points at
half-step `a i` on either side of the center. -/
@[simp] theorem symmetricMixedDifference_singleton
    {V P A ι : Type*} [AddCommGroup V] [AddAction V P] [AddCommGroup A]
    (a : ι → V) (i : ι) (f : P → A) (x : P) :
    symmetricMixedDifference a {i} f x =
      f (a i +ᵥ x) - f ((-a i) +ᵥ x) := by
  classical
  rw [symmetricMixedDifference, mixedDifference_singleton]
  simp only [Finset.sum_singleton]
  have hlower : -(2 • a i) +ᵥ (a i +ᵥ x) = (-a i) +ᵥ x := by
    calc
      -(2 • a i) +ᵥ (a i +ᵥ x) = (-(2 • a i) + a i) +ᵥ x :=
        (add_vadd _ _ _).symm
      _ = (-a i) +ᵥ x := by
        congr 1
        abel
  rw [hlower]

/-- Peeling one half-step gives the usual centered recurrence: the remaining
operator is evaluated once at `a i +ᵥ x` and once at `(-a i) +ᵥ x`.
Distinct indices may still carry equal half-step values. -/
theorem symmetricMixedDifference_insert
    {V P A ι : Type*} [AddCommGroup V] [AddAction V P] [AddCommGroup A]
    [DecidableEq ι] (a : ι → V) (s : Finset ι) (f : P → A) (x : P)
    {i : ι} (hi : i ∉ s) :
    symmetricMixedDifference a (insert i s) f x =
      symmetricMixedDifference a s f (a i +ᵥ x) -
        symmetricMixedDifference a s f ((-a i) +ᵥ x) := by
  classical
  unfold symmetricMixedDifference
  rw [Finset.sum_insert hi, mixedDifference_insert (hi := hi)]
  have hupper :
      (a i + ∑ j ∈ s, a j) +ᵥ x =
        (∑ j ∈ s, a j) +ᵥ (a i +ᵥ x) := by
    calc
      (a i + ∑ j ∈ s, a j) +ᵥ x =
          ((∑ j ∈ s, a j) + a i) +ᵥ x := by rw [add_comm]
      _ = (∑ j ∈ s, a j) +ᵥ (a i +ᵥ x) := add_vadd _ _ _
  have hlower :
      -(2 • a i) +ᵥ ((a i + ∑ j ∈ s, a j) +ᵥ x) =
        (∑ j ∈ s, a j) +ᵥ ((-a i) +ᵥ x) := by
    calc
      -(2 • a i) +ᵥ ((a i + ∑ j ∈ s, a j) +ᵥ x) =
          (-(2 • a i) + (a i + ∑ j ∈ s, a j)) +ᵥ x :=
        (add_vadd _ _ _).symm
      _ = ((∑ j ∈ s, a j) + -a i) +ᵥ x := by
        congr 1
        abel
      _ = (∑ j ∈ s, a j) +ᵥ ((-a i) +ᵥ x) := add_vadd _ _ _
  rw [hlower, hupper]

/-- **Symmetric Boolean-cube expansion.**  Each subset `t ⊆ s` selects
the lower endpoint in precisely the coordinates in `t`, hence the corner
`(∑_{i∈s} a i) - 2(∑_{i∈t} a i) +ᵥ x` and the sign `(-1)^|t|`. -/
theorem symmetricMixedDifference_eq_sum_powerset_smul
    {V P A ι : Type*} [AddCommGroup V] [AddAction V P] [AddCommGroup A]
    (a : ι → V) (s : Finset ι) (f : P → A) (x : P) :
    symmetricMixedDifference a s f x =
      ∑ t ∈ s.powerset, ((-1 : ℤ) ^ t.card) •
        f (((∑ i ∈ s, a i) - 2 • (∑ i ∈ t, a i)) +ᵥ x) := by
  rw [symmetricMixedDifference, mixedDifference_eq_sum_powerset_smul]
  refine Finset.sum_congr rfl fun t _ht ↦ ?_
  have hstep : ∑ i ∈ t, -(2 • a i) = -(2 • (∑ i ∈ t, a i)) := by
    rw [Finset.sum_neg_distrib, ← Finset.smul_sum]
  have hpoint :
      (∑ i ∈ t, -(2 • a i)) +ᵥ ((∑ i ∈ s, a i) +ᵥ x) =
        ((∑ i ∈ s, a i) - 2 • (∑ i ∈ t, a i)) +ᵥ x := by
    rw [hstep]
    calc
      -(2 • (∑ i ∈ t, a i)) +ᵥ ((∑ i ∈ s, a i) +ᵥ x) =
          (-(2 • (∑ i ∈ t, a i)) + ∑ i ∈ s, a i) +ᵥ x :=
        (add_vadd _ _ _).symm
      _ = ((∑ i ∈ s, a i) - 2 • (∑ i ∈ t, a i)) +ᵥ x := by
        congr 1
        abel
  rw [hpoint]

/-- **Sharp symmetric polynomial extraction.**  If `p` has degree at most
the number of half-steps, the symmetric operator extracts its coefficient in
that degree.  The orientation sign of the ordinary mixed difference cancels
the sign contributed by the negative full steps, leaving a sign-free factor. -/
theorem symmetricMixedDifference_polynomial_eq_coeff_card
    {R ι : Type*} [CommRing R] (a : ι → R) (s : Finset ι)
    (p : R[X]) (hdeg : p.natDegree ≤ s.card) (x : R) :
    symmetricMixedDifference a s (fun y ↦ p.eval y) x =
      p.coeff s.card *
        ((s.card.factorial : R) * ∏ i ∈ s, (2 : ℕ) • a i) := by
  unfold symmetricMixedDifference
  rw [mixedDifference_polynomial_eq_coeff_card (hdeg := hdeg), Finset.prod_neg]
  have hsign : (-1 : R) ^ s.card * (-1 : R) ^ s.card = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  calc
    p.coeff s.card *
          ((-1 : R) ^ s.card * (s.card.factorial : R) *
            ((-1 : R) ^ s.card * ∏ i ∈ s, (2 : ℕ) • a i)) =
        p.coeff s.card *
          (((-1 : R) ^ s.card * (-1 : R) ^ s.card) *
            ((s.card.factorial : R) * ∏ i ∈ s, (2 : ℕ) • a i)) := by
      ring
    _ = p.coeff s.card *
        ((s.card.factorial : R) * ∏ i ∈ s, (2 : ℕ) • a i) := by
      rw [hsign, one_mul]

/-- **Symmetric Prouhet cancellation.**  A symmetric mixed difference
annihilates every polynomial whose `Polynomial.degree` is below the number
of active half-steps.  The degree-valued hypothesis includes the genuine
empty-set boundary, where the zero polynomial is the sole possibility. -/
theorem symmetricMixedDifference_polynomial_of_degree_lt
    {R ι : Type*} [CommRing R] (a : ι → R) (s : Finset ι)
    (p : R[X]) (hdeg : p.degree < (s.card : WithBot ℕ)) (x : R) :
    symmetricMixedDifference a s (fun y ↦ p.eval y) x = 0 := by
  classical
  by_cases hp : p = 0
  · subst p
    rw [symmetricMixedDifference_polynomial_eq_coeff_card a s 0 (by simp) x]
    simp
  · have hnat : p.natDegree < s.card :=
      (Polynomial.natDegree_lt_iff_degree_lt hp).2 hdeg
    rw [symmetricMixedDifference_polynomial_eq_coeff_card a s p hnat.le x,
      Polynomial.coeff_eq_zero_of_natDegree_lt hnat, zero_mul]

/-- The first surviving symmetric monomial moment has no orientation sign:
the `|s|`-th power evaluates to `|s|!` times the product of the full steps
`2 • a i`, independently of the center. -/
theorem symmetricMixedDifference_pow_card
    {R ι : Type*} [CommRing R] (a : ι → R) (s : Finset ι) (x : R) :
    symmetricMixedDifference a s (fun y ↦ y ^ s.card) x =
      (s.card.factorial : R) * ∏ i ∈ s, (2 : ℕ) • a i := by
  simpa only [Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.coeff_X_pow_self, one_mul] using
      symmetricMixedDifference_polynomial_eq_coeff_card a s
        (Polynomial.X ^ s.card : R[X])
        (Polynomial.natDegree_X_pow_le s.card) x

/-! ## Dyadic half-steps -/

/-- The symmetric mixed difference with dyadic half-steps
`h, 2h, ..., 2^(m-1)h`. -/
def symmetricDyadicMixedDifference {M A : Type*} [AddCommGroup M]
    [AddCommGroup A] (h : M) (m : ℕ) (f : M → A) (x : M) : A :=
  symmetricMixedDifference (fun j : ℕ ↦ 2 ^ j • h) (range m) f x

/-- The zeroth symmetric dyadic difference is evaluation at the center. -/
@[simp] theorem symmetricDyadicMixedDifference_zero
    {M A : Type*} [AddCommGroup M] [AddCommGroup A]
    (h : M) (f : M → A) (x : M) :
    symmetricDyadicMixedDifference h 0 f x = f x := by
  simp [symmetricDyadicMixedDifference]

/-- **Centered Thue--Morse block identity.**  Starting at the upper corner
`∑_{j<m} 2^j h + x`, the integer `n` chooses the lower endpoint in exactly
its nonzero binary coordinates.  Thus the ordinary Thue--Morse sign is the
orientation sign of the corresponding symmetric Boolean-cube corner. -/
theorem symmetricDyadicMixedDifference_eq_sum_thueMorseSign_smul
    {M A : Type*} [AddCommGroup M] [AddCommGroup A]
    (h : M) (m : ℕ) (f : M → A) (x : M) :
    symmetricDyadicMixedDifference h m f x =
      ∑ n ∈ range (2 ^ m), thueMorseSign n •
        f (((∑ j ∈ range m, 2 ^ j • h) + x) + n • (-(2 • h))) := by
  rw [sum_thueMorseSign_smul_eq_mixedDifference
    (-(2 • h)) f m ((∑ j ∈ range m, 2 ^ j • h) + x)]
  unfold symmetricDyadicMixedDifference symmetricMixedDifference
  unfold dyadicMixedDifference
  simp only [vadd_eq_add]
  apply congrArg
    (fun step : ℕ → M ↦ mixedDifference step (range m) f
      ((∑ j ∈ range m, 2 ^ j • h) + x))
  funext j
  rw [smul_neg, smul_smul, smul_smul, Nat.mul_comm 2 (2 ^ j)]

/-- **Increasing-grid Thue--Morse corner.**  Over a characteristic-zero field, take
the least half-step to be `2⁻ᵐ`.  Reversing the descending block in
`symmetricDyadicMixedDifference_eq_sum_thueMorseSign_smul` produces the
Thue--Morse complement factor `(-1)^m` and the increasing affine grid

`x - (1 - 2⁻ᵐ) + 2n · 2⁻ᵐ`,  `0 ≤ n < 2^m`.

This common-denominator form is valid also at `m = 0`; for positive `m` its
grid increment is exactly `n / 2^(m-1)`.  No binary calculation is repeated here:
the proof is just `Finset.sum_range_reflect`, the existing complement theorem
`thueMorseSign_dyadic_complement`, and the finite geometric sum. -/
theorem symmetricDyadicMixedDifference_inv_two_pow_eq_sum_thueMorseSign_smul
    {R A : Type*} [Field R] [CharZero R] [AddCommGroup A]
    (m : ℕ) (f : R → A) (x : R) :
    symmetricDyadicMixedDifference (((2 : R) ^ m)⁻¹) m f x =
      ∑ n ∈ range (2 ^ m),
        ((-1 : ℤ) ^ m * thueMorseSign n) •
          f (x - (1 - ((2 : R) ^ m)⁻¹) +
            (2 * (n : R)) * ((2 : R) ^ m)⁻¹) := by
  rw [symmetricDyadicMixedDifference_eq_sum_thueMorseSign_smul]
  let h : R := ((2 : R) ^ m)⁻¹
  have hpow : (2 : R) ^ m ≠ 0 := pow_ne_zero m (by norm_num)
  have hgeom : ∑ j ∈ range m, 2 ^ j = 2 ^ m - 1 := by
    simpa using (Nat.geomSum_eq (m := 2) (by norm_num) m)
  have hsum : ∑ j ∈ range m, 2 ^ j • h = 1 - h := by
    calc
      ∑ j ∈ range m, 2 ^ j • h = (2 ^ m - 1) • h := by
        rw [Finset.sum_nsmul_assoc, hgeom]
      _ = (((2 ^ m - 1 : ℕ) : R)) * h := by rw [nsmul_eq_mul]
      _ = ((2 : R) ^ m - 1) * h := by
        rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow]
        norm_num
      _ = 1 - h := by
        dsimp only [h]
        field_simp
  calc
    ∑ n ∈ range (2 ^ m), thueMorseSign n •
          f (((∑ j ∈ range m, 2 ^ j • h) + x) + n • (-(2 • h))) =
        ∑ n ∈ range (2 ^ m), thueMorseSign (2 ^ m - 1 - n) •
          f (((∑ j ∈ range m, 2 ^ j • h) + x) +
            (2 ^ m - 1 - n) • (-(2 • h))) := by
      exact (Finset.sum_range_reflect
        (fun n ↦ thueMorseSign n •
          f (((∑ j ∈ range m, 2 ^ j • h) + x) + n • (-(2 • h))))
        (2 ^ m)).symm
    _ = ∑ n ∈ range (2 ^ m),
          ((-1 : ℤ) ^ m * thueMorseSign n) •
            f (x - (1 - h) + (2 * (n : R)) * h) := by
      refine Finset.sum_congr rfl fun n hn ↦ ?_
      have hnlt : n < 2 ^ m := Finset.mem_range.mp hn
      have hnle : n ≤ 2 ^ m - 1 := by omega
      have hcast : ((2 ^ m - 1 - n : ℕ) : R) =
          (2 : R) ^ m - 1 - (n : R) := by
        rw [Nat.cast_sub hnle, Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow]
        norm_num
      have hpoint :
          ((∑ j ∈ range m, 2 ^ j • h) + x) +
              (2 ^ m - 1 - n) • (-(2 • h)) =
            x - (1 - h) + (2 * (n : R)) * h := by
        rw [hsum]
        simp only [nsmul_eq_mul, hcast]
        dsimp only [h]
        field_simp
        ring
      rw [thueMorseSign_dyadic_complement m n hnlt, hpoint]
    _ = ∑ n ∈ range (2 ^ m),
          ((-1 : ℤ) ^ m * thueMorseSign n) •
            f (x - (1 - ((2 : R) ^ m)⁻¹) +
              (2 * (n : R)) * ((2 : R) ^ m)⁻¹) := by
      rfl

/-- The increasing-grid corner in the report's displayed positive-order
form.  Writing the number of differences as `m + 1` avoids a truncated
natural subtraction: the mesh is exactly `1 / 2^m`, i.e. `1 / 2^(N-1)`
when `N = m + 1`. -/
theorem symmetricDyadicMixedDifference_inv_two_pow_succ_eq_sum_thueMorseSign_smul
    {R A : Type*} [Field R] [CharZero R] [AddCommGroup A]
    (m : ℕ) (f : R → A) (x : R) :
    symmetricDyadicMixedDifference (((2 : R) ^ (m + 1))⁻¹) (m + 1) f x =
      ∑ n ∈ range (2 ^ (m + 1)),
        ((-1 : ℤ) ^ (m + 1) * thueMorseSign n) •
          f (x - (1 - ((2 : R) ^ (m + 1))⁻¹) +
            (n : R) / (2 : R) ^ m) := by
  rw [symmetricDyadicMixedDifference_inv_two_pow_eq_sum_thueMorseSign_smul]
  refine Finset.sum_congr rfl fun n _hn ↦ ?_
  have hmesh :
      (2 * (n : R)) * ((2 : R) ^ (m + 1))⁻¹ =
        (n : R) / (2 : R) ^ m := by
    rw [pow_succ]
    field_simp
  rw [hmesh]

end Fabius
