import FabiusFunction.FinitePolynomialFunctional
import FabiusFunction.FiniteQBinomialCore
import FabiusFunction.ThueMorsePrefix
import Mathlib.Tactic.FieldSimp

/-!
# Finite q-Pochhammer symbols and Gaussian binomials at `q = 1/2`

This module is the small q-special-function layer in which the
q-binomial--Thue--Morse closed form for dyadic Fabius values is stated.  Over
`ℚ` it defines the finite q-Pochhammer symbol

`(a; q)_n = ∏_{j=0}^{n-1} (1 - a q^j)`

as `finiteQPochhammer a q n`, in Wolfram Language's argument order, and the
Gaussian binomial `qBinomial n k q = (q;q)_n / ((q;q)_k (q;q)_{n-k})`,
extended by zero for `k > n`.  Both are specialized at `q = 1/2` to
`halfQPochhammer n = (1/2; 1/2)_n` and `halfQBinomial n k`.  All arithmetic
is exact and rational; there is no polynomial-in-`q` theory here.

The payload is the finite q-binomial theorem at `q = 1/2`,

`∑_{k=0}^n (-1)^k (1/2)^(C(k,2)) * halfQBinomial n k * z^k = (z; 1/2)_n`,

proved from the q-Pascal recurrence, together with its values at the dyadic
nodes `z = 2^m`.  More generally, its complete rational root locus is
`z = 2^j` for `j < n`; scalar extension preserves this classification at
the embedded rational points of every field over `ℚ`.  At a dyadic node below
degree, the corresponding factor `1 - 2^m (1/2)^m` vanishes; for `n ≤ m`
the product is an exact signed quotient of Mersenne products.  At `z = 2^n`
this specializes to
`(-1)^n 2^(C(n+1,2)) (1/2;1/2)_n`.  The vanishing and endpoint evaluations are the
interpolation data that the public weights `halfQBinomialDyadicWeight` feed
to the negative nodes `negativeDyadicNode k = -(2^k)`.  Their weighted sum
annihilates every polynomial of degree below `n` and extracts the coefficient
of degree `n` with the exact q-Pochhammer, equivalently Mersenne-product,
factor.  `FabiusFunction.FabiusQBinomialFormula` feeds the same data to its
Lagrange argument, and the q-binomial theorem itself is what
`FabiusFunction.FabiusDiscreteLimitToeplitz` evaluates at `z = 1/2` and
`z = -1/2` to obtain its Toeplitz row sums and their exact total variation.
These definitions are also the notation carried unchanged through the
statements of the whole `Fabius*QBinomial*` family.

## Main results

* `finiteQPochhammer`, `qPochhammer`, `halfQPochhammer` -- the symbol, its
  notation-faithful Wolfram alias, and the `q = 1/2` case, with
  `halfQPochhammer_pos` and `halfQPochhammer_ne_zero` supplying the
  nonvanishing that every later denominator argument needs.
* `qBinomial`, `qBinomial_eq_quotient`, `qBinomial_symm`, `halfQBinomial`,
  `halfQBinomial_pos`, `halfQBinomial_symm`, `qBinomial_half_eq_zero_iff`,
  `gaussianBinomial_half_eq_halfQBinomial`, `halfQBinomial_succ_succ`,
  `halfQBinomial_succ_succ'` -- the generic quotient and reflection,
  their `q = 1/2` specialization and zero locus, positivity for
  `k ≤ n`, the identification with the denominator-free Gaussian
  coefficient of
  `FiniteQBinomialCore`, and both orientations of the q-Pascal
  recurrence, inherited from that core through the identification.
* `halfQBinomial_theorem` -- the q-binomial theorem displayed above.
* `finiteQPochhammerIn_eq_zero_iff`, `finiteQPochhammer_eq_zero_iff`,
  `finiteQPochhammerIn_half_eq_zero_iff`,
  `finiteQPochhammer_half_eq_zero_iff`,
  `halfQBinomial_sum_eq_zero_iff`, and
  `qBinomial_half_sum_eq_zero_iff` -- the product-zero criterion over
  every nontrivial ring without zero divisors, the complete root locus
  `2^j` for `j < n` at `q = 1/2` in every field of characteristic zero,
  and their rational instances.
* `qBinomial_half_sum_algebraMap_eq_zero_iff` -- the same root locus after
  embedding the rational argument and coefficients in an arbitrary field
  over `ℚ`.
* `halfQBinomial_two_pow_sum_eq_qPochhammer` -- the all-index dyadic-node
  specialization, with an exact piecewise Mersenne-product form and the
  existing zero/endpoint interpolation boundaries.
* `sum_gaussianWeight_mul_neg_inv_pow` -- the field-level node/weight
  identity: the signed Gaussian weights at the nodes `-(q⁻¹)^k` have
  the monomial moments `(-1)^d (q^(-d); q)_n`.
* `halfQBinomialDyadicWeight`, `negativeDyadicNode`,
  `halfQBinomialDyadicWeight_nodes_pow`,
  `halfQBinomialDyadicWeight_nodes_zero`, and
  `halfQBinomialDyadicWeight_nodes_self` -- the signed Gaussian weights,
  their negative dyadic nodes, and the all-degree, lower, and top
  monomial moments.
* `halfQBinomial_negativeDyadic_polynomial_sum_eq_coeff` -- the
  degree-valued Gaussian/Prouhet extractor, including the zero-polynomial
  boundary, with q-Pochhammer and Mersenne-product right-hand sides.
* `qPochhammer_two_pow_eq_mersenne_div` and `qPochhammer_two_pow_eq_ite` --
  the closed Mersenne-product value at every dyadic node.
* `four_pow_choose_two_semiring` and `four_pow_choose_two` --
  `4^(C(k,2)) = 2^(k(k-1))` in every semiring and over `ℚ`, which
  rewrites the Wolfram denominator as a pure power of two.

The remaining declarations are edge-case `simp` lemmas, `qBinomial_half_*`
restatements of the results above in literal Wolfram notation, and a
Mersenne-product normalization layer: `halfMersenneProduct n` is
`∏_{j=1}^n (2^j - 1)`, `halfQPochhammer_eq_mersenne_div` gives
`(1/2;1/2)_n = (∏_{j=1}^n (2^j - 1)) / 2^(C(n+1,2))`, and
`two_pow_nat_sq_mul_halfQPochhammer` reads the formula's prefactor
division-free as `2^(n^2) (1/2;1/2)_n = 2^(C(n,2)) ∏_{j=1}^n (2^j - 1)`.

Caveat: `qBinomial n k q` is the q-Pochhammer quotient, not the polynomial
Gaussian binomial.  The two agree whenever the denominator is nonzero, which
holds at `q = 1/2`, the only specialization used here.  When the denominator
vanishes---as it can at roots of unity---the quotient definition can instead
disagree with the polynomial continuation.  Natural subtraction is
truncated, so the quotient lemmas carry
`k ≤ n` hypotheses, and `C(k,2)` above is Lean's `k.choose 2`.  The base
root-locus theorems classify rational arguments, the scalar-extension
form classifies their images in fields over `ℚ`, and
`finiteQPochhammerIn_half_eq_zero_iff` classifies arbitrary arguments in
every field of characteristic zero; root multiplicities are not packaged
here.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

/-- The finite Wolfram-language `QPochhammer[a,q,n]`, over `ℚ`. -/
noncomputable def finiteQPochhammer (a q : ℚ) (n : ℕ) : ℚ :=
  ∏ j ∈ Finset.range n, (1 - a * q ^ j)

/-- The generic commutative-ring q-Pochhammer product specializes
definitionally to the established rational API. -/
@[simp] theorem finiteQPochhammerIn_rat_eq (a q : ℚ) (n : ℕ) :
    finiteQPochhammerIn a q n = finiteQPochhammer a q n := by
  rfl

/-- The empty finite q-Pochhammer product is one. -/
@[simp] theorem finiteQPochhammer_zero (a q : ℚ) :
    finiteQPochhammer a q 0 = 1 := by
  simp [finiteQPochhammer]

/-- Peeling the top factor: `(a; q)_(n+1) = (a; q)_n (1 - a q^n)`, the new
factor carrying the exponent `n`, the last index of `range (n + 1)`.  This
is the induction step behind `halfQPochhammer_succ` and behind the closing
step of `halfQBinomial_theorem`. -/
theorem finiteQPochhammer_succ (a q : ℚ) (n : ℕ) :
    finiteQPochhammer a q (n + 1) =
      finiteQPochhammer a q n * (1 - a * q ^ n) := by
  simp [finiteQPochhammer, Finset.prod_range_succ]

/-- Public notation-faithful alias for Wolfram Language's finite
`QPochhammer[a,q,n]`. -/
noncomputable abbrev qPochhammer := finiteQPochhammer

/-- The empty q-Pochhammer product, in notation-faithful form, is one. -/
@[simp] theorem qPochhammer_zero (a q : ℚ) : qPochhammer a q 0 = 1 := by
  exact finiteQPochhammer_zero a q

/-- The same top-factor recurrence stated for the Wolfram alias, so that
statements written in literal `QPochhammer` notation never have to unfold to
`finiteQPochhammer`. -/
theorem qPochhammer_succ (a q : ℚ) (n : ℕ) :
    qPochhammer a q (n + 1) =
      qPochhammer a q n * (1 - a * q ^ n) :=
  finiteQPochhammer_succ a q n

/-- A finite q-Pochhammer product over a nontrivial commutative ring
without zero divisors vanishes exactly when one of its factors vanishes.
No nonzero or positivity hypothesis on `q` is needed. -/
theorem finiteQPochhammerIn_eq_zero_iff
    {R : Type*} [CommRing R] [NoZeroDivisors R] [Nontrivial R]
    (a q : R) (n : ℕ) :
    finiteQPochhammerIn a q n = 0 ↔
      ∃ j < n, a * q ^ j = 1 := by
  unfold finiteQPochhammerIn
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨j, hj, hzero⟩
    exact ⟨j, Finset.mem_range.mp hj, (sub_eq_zero.mp hzero).symm⟩
  · rintro ⟨j, hj, hone⟩
    exact ⟨j, Finset.mem_range.mpr hj, sub_eq_zero.mpr hone.symm⟩

/-- A finite q-Pochhammer product vanishes exactly when one of its
factors vanishes.  No nonzero or positivity hypothesis on `q` is needed.
This is the rational instance of `finiteQPochhammerIn_eq_zero_iff`. -/
theorem finiteQPochhammer_eq_zero_iff (a q : ℚ) (n : ℕ) :
    finiteQPochhammer a q n = 0 ↔
      ∃ j < n, a * q ^ j = 1 :=
  finiteQPochhammerIn_eq_zero_iff a q n

private theorem mul_half_pow_eq_one_iff
    {K : Type*} [Field K] [CharZero K] (z : K) (j : ℕ) :
    z * (1 / 2 : K) ^ j = 1 ↔ z = (2 : K) ^ j := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have hcancel : (2 : K) ^ j * (1 / 2 : K) ^ j = 1 := by
    rw [← mul_pow, mul_one_div_cancel h2, one_pow]
  constructor
  · intro h
    apply mul_right_cancel₀ (pow_ne_zero j (one_div_ne_zero h2))
    rw [h, hcancel]
  · rintro rfl
    exact hcancel

/-- **Root locus of `(z; 1/2)_n` in characteristic zero.**  In every
field of characteristic zero, the finite q-Pochhammer product at
`q = 1/2` vanishes at exactly the points `2^j` with `j < n`.  The
argument `z` is an arbitrary element of the field, not merely the image
of a rational. -/
theorem finiteQPochhammerIn_half_eq_zero_iff
    {K : Type*} [Field K] [CharZero K] (z : K) (n : ℕ) :
    finiteQPochhammerIn z (1 / 2 : K) n = 0 ↔
      ∃ j < n, z = (2 : K) ^ j := by
  rw [finiteQPochhammerIn_eq_zero_iff]
  constructor
  · rintro ⟨j, hj, hterm⟩
    exact ⟨j, hj, (mul_half_pow_eq_one_iff z j).1 hterm⟩
  · rintro ⟨j, hj, hz⟩
    exact ⟨j, hj, (mul_half_pow_eq_one_iff z j).2 hz⟩

/-- At `q = 1/2`, the finite q-Pochhammer product vanishes at exactly
the rational points `2^j` with `j < n`; the rational instance of
`finiteQPochhammerIn_half_eq_zero_iff`. -/
theorem finiteQPochhammer_half_eq_zero_iff (z : ℚ) (n : ℕ) :
    finiteQPochhammer z (1 / 2) n = 0 ↔
      ∃ j < n, z = (2 : ℚ) ^ j :=
  finiteQPochhammerIn_half_eq_zero_iff z n

/-- The specialization `QPochhammer[1/2,1/2,n]`. -/
noncomputable def halfQPochhammer (n : ℕ) : ℚ :=
  finiteQPochhammer (1 / 2) (1 / 2) n

/-- The literal q-Pochhammer alias at `a = q = 1/2` is `halfQPochhammer`. -/
@[simp] theorem qPochhammer_half_eq (n : ℕ) :
    qPochhammer (1 / 2) (1 / 2) n = halfQPochhammer n := by
  rfl

/-- The empty q-Pochhammer product at `q = 1/2` is one. -/
@[simp] theorem halfQPochhammer_zero : halfQPochhammer 0 = 1 := by
  simp [halfQPochhammer]

/-- Top-factor recurrence at `q = 1/2`, with the two halves already merged:
the new factor is `1 - (1/2)^(n+1)`, not `1 - (1/2) (1/2)^n`.  This is the
form the Toeplitz row estimates of `FabiusDiscreteLimitToeplitz` induct
on. -/
theorem halfQPochhammer_succ (n : ℕ) :
    halfQPochhammer (n + 1) =
      halfQPochhammer n * (1 - (1 / 2 : ℚ) ^ (n + 1)) := by
  rw [halfQPochhammer, finiteQPochhammer_succ]
  congr 2
  rw [pow_succ]
  ring

/-- `(1/2; 1/2)_n` is strictly positive, every factor `1 - (1/2)^(j+1)`
lying in `(0, 1)`.  This is what lets `FabiusDiscreteLimitToeplitz` drop the
absolute value from the denominator of a Toeplitz coefficient. -/
theorem halfQPochhammer_pos (n : ℕ) : 0 < halfQPochhammer n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [halfQPochhammer_succ]
      apply mul_pos ih
      have hpow : (1 / 2 : ℚ) ^ (n + 1) < 1 :=
        pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
      linarith

/-- `(1/2; 1/2)_n` never vanishes.  It sits in the denominator of every
q-binomial quotient below, so this is the side condition discharged by the
`field_simp` calls here and throughout the `Fabius*QBinomial*` files. -/
theorem halfQPochhammer_ne_zero (n : ℕ) : halfQPochhammer n ≠ 0 :=
  (halfQPochhammer_pos n).ne'

/-- Product of the Mersenne factors `2^j - 1`, for `1 ≤ j ≤ n`. -/
noncomputable def halfMersenneProduct (n : ℕ) : ℚ :=
  ∏ j ∈ Finset.range n, ((2 : ℚ) ^ (j + 1) - 1)

/-- The empty product of Mersenne factors is one. -/
@[simp] theorem halfMersenneProduct_zero : halfMersenneProduct 0 = 1 := by
  simp [halfMersenneProduct]

/-- Peeling the top Mersenne factor:
`∏_(j=1)^(n+1) (2^j - 1) = (∏_(j=1)^n (2^j - 1)) (2^(n+1) - 1)`.  This is the
induction step of `halfQPochhammer_eq_mersenne_div`. -/
theorem halfMersenneProduct_succ (n : ℕ) :
    halfMersenneProduct (n + 1) =
      halfMersenneProduct n * ((2 : ℚ) ^ (n + 1) - 1) := by
  simp [halfMersenneProduct, Finset.prod_range_succ]

/-- Split the first `m + n` Mersenne factors after the first `m` factors. -/
theorem halfMersenneProduct_add (m n : ℕ) :
    halfMersenneProduct (m + n) =
      halfMersenneProduct m *
        ∏ j ∈ Finset.range n, ((2 : ℚ) ^ (m + j + 1) - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ, halfMersenneProduct_succ, ih,
        Finset.prod_range_succ]
      ring

/-- `∏_(j=1)^n (2^j - 1)` is strictly positive, since every factor with
`j ≥ 1` is at least `1`. -/
theorem halfMersenneProduct_pos (n : ℕ) : 0 < halfMersenneProduct n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [halfMersenneProduct_succ]
      exact mul_pos ih (by
        have : (1 : ℚ) < 2 ^ (n + 1) := one_lt_pow₀ (by norm_num) (by omega)
        linarith)

/-- The Mersenne product never vanishes; this is the side condition needed
by the `field_simp` in `halfQBinomial_eq_mersenne`. -/
theorem halfMersenneProduct_ne_zero (n : ℕ) : halfMersenneProduct n ≠ 0 :=
  (halfMersenneProduct_pos n).ne'

private theorem half_factor_eq (m : ℕ) :
    1 - (1 / 2 : ℚ) ^ m = ((2 : ℚ) ^ m - 1) / (2 : ℚ) ^ m := by
  rw [div_pow]
  simp only [one_pow]
  field_simp

/-- The exact denominator normalization of `(1/2;1/2)_n`. -/
theorem halfQPochhammer_eq_mersenne_div (n : ℕ) :
    halfQPochhammer n =
      halfMersenneProduct n / (2 : ℚ) ^ ((n + 1).choose 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hchoose : (n + 2).choose 2 = (n + 1).choose 2 + (n + 1) := by
        simpa only [Nat.succ_eq_add_one] using choose_succ_two (n + 1)
      rw [halfQPochhammer_succ, halfMersenneProduct_succ, ih,
        half_factor_eq, hchoose, pow_add]
      ring

/-- The full prefactor denominator in the requested formula has no hidden
division: `2^(n^2) (1/2;1/2)_n = 2^(choose n 2) ∏_{j=1}^n (2^j-1)`. -/
theorem two_pow_sq_mul_halfQPochhammer (n : ℕ) :
    (2 : ℚ) ^ (n * n) * halfQPochhammer n =
      (2 : ℚ) ^ (n.choose 2) * halfMersenneProduct n := by
  rw [halfQPochhammer_eq_mersenne_div, choose_square_split, pow_add]
  field_simp

/-- The same normalization, with the Wolfram expression `n^2` transcribed
literally as a natural-number square. -/
theorem two_pow_nat_sq_mul_halfQPochhammer (n : ℕ) :
    (2 : ℚ) ^ (n ^ 2) * halfQPochhammer n =
      (2 : ℚ) ^ (n.choose 2) * halfMersenneProduct n := by
  simpa [pow_two] using two_pow_sq_mul_halfQPochhammer n

/-- Normalization of the reciprocal prefactor in the requested formula. -/
theorem one_div_two_pow_nat_sq_mul_halfQPochhammer (n : ℕ) :
    1 / ((2 : ℚ) ^ (n ^ 2) * halfQPochhammer n) =
      1 / ((2 : ℚ) ^ (n.choose 2) * halfMersenneProduct n) := by
  rw [two_pow_nat_sq_mul_halfQPochhammer]

/-- The Wolfram denominator `4^Binomial[k,2]` as a pure power of two,
in every semiring. -/
theorem four_pow_choose_two_semiring
    {R : Type*} [Semiring R] (k : ℕ) :
    (4 : R) ^ (k.choose 2) = (2 : R) ^ (k * (k - 1)) := by
  have htwo : 2 * k.choose 2 = k * (k - 1) := by
    cases k with
    | zero => simp
    | succ k =>
        simpa [mul_comm] using two_mul_choose_succ_two k
  calc
    (4 : R) ^ (k.choose 2) = ((2 : R) ^ 2) ^ (k.choose 2) := by
      norm_num
    _ = (2 : R) ^ (2 * k.choose 2) := by rw [pow_mul]
    _ = (2 : R) ^ (k * (k - 1)) := by rw [htwo]

/-- The Wolfram denominator `4^Binomial[k,2]` as a pure power of two;
the rational instance of `four_pow_choose_two_semiring`. -/
theorem four_pow_choose_two (k : ℕ) :
    (4 : ℚ) ^ (k.choose 2) = (2 : ℚ) ^ (k * (k - 1)) :=
  four_pow_choose_two_semiring k

/-- `QBinomial[n,k,1/2]`, extended by zero for `k > n`. -/
noncomputable def halfQBinomial (n k : ℕ) : ℚ :=
  if k ≤ n then
    halfQPochhammer n /
      (halfQPochhammer k * halfQPochhammer (n - k))
  else 0

/-- The q-Pochhammer quotient presentation of Wolfram Language's
`QBinomial[n,k,q]` over `ℚ`, extended by zero when `k > n`.  This agrees with
the polynomial continuation whenever the denominator is nonzero; in
particular, it is exact at the specialization `q = 1/2` used below. -/
noncomputable def qBinomial (n k : ℕ) (q : ℚ) : ℚ :=
  if k ≤ n then
    qPochhammer q q n /
      (qPochhammer q q k * qPochhammer q q (n - k))
  else 0

/-- The specialization `QBinomial[n,k,1/2] = halfQBinomial n k`, true by
`rfl`.  It is the bridge by which the literal-notation statements used in
`FabiusQBinomialFormula` are discharged from the `halfQBinomial` lemmas. -/
theorem qBinomial_half_eq (n k : ℕ) :
    qBinomial n k (1 / 2) = halfQBinomial n k := by
  rfl

/-- Extension by zero: `QBinomial[n,k,q] = 0` whenever `n < k`, for every
`q`.  This records the `if` in the definition and says nothing about `q`. -/
theorem qBinomial_eq_zero_of_lt (q : ℚ) {n k : ℕ} (hk : n < k) :
    qBinomial n k q = 0 := by
  simp [qBinomial, Nat.not_le.mpr hk]

/-- In the admissible range, the generic q-binomial is its defining
q-Pochhammer quotient. -/
theorem qBinomial_eq_quotient (q : ℚ) {n k : ℕ} (hk : k ≤ n) :
    qBinomial n k q =
      qPochhammer q q n /
        (qPochhammer q q k * qPochhammer q q (n - k)) := by
  simp [qBinomial, hk]

/-- In the admissible range `k ≤ n` the `if` unfolds and `halfQBinomial n k`
is the q-Pochhammer quotient
`(1/2;1/2)_n / ((1/2;1/2)_k (1/2;1/2)_(n-k))`.  The hypothesis `k ≤ n` is
needed because `n - k` is truncated natural subtraction.  Every quotient
manipulation below starts from this rewrite. -/
theorem halfQBinomial_eq_quotient {n k : ℕ} (hk : k ≤ n) :
    halfQBinomial n k =
      halfQPochhammer n /
        (halfQPochhammer k * halfQPochhammer (n - k)) := by
  simpa only [qBinomial_half_eq, qPochhammer_half_eq] using
    qBinomial_eq_quotient (1 / 2) hk

/-- The coefficient vanishes above the diagonal, `n < k`.  This is what
kills the extra term when a sum over `range (n + 1)` is compared with a sum
over `range (n + 2)` in the induction proving `halfQBinomial_theorem`. -/
theorem halfQBinomial_eq_zero_of_lt {n k : ℕ} (hk : n < k) :
    halfQBinomial n k = 0 := by
  simp [halfQBinomial, Nat.not_le.mpr hk]

/-- The lower-edge Gaussian coefficient `halfQBinomial n 0` is one. -/
@[simp] theorem halfQBinomial_zero_right (n : ℕ) :
    halfQBinomial n 0 = 1 := by
  rw [halfQBinomial_eq_quotient (Nat.zero_le n)]
  simp [halfQPochhammer_ne_zero]

/-- The diagonal Gaussian coefficient `halfQBinomial n n` is one. -/
@[simp] theorem halfQBinomial_self (n : ℕ) :
    halfQBinomial n n = 1 := by
  rw [halfQBinomial_eq_quotient (le_refl n)]
  simp [halfQPochhammer_ne_zero]

/-- The Gaussian coefficient at the origin is one. -/
@[simp] theorem halfQBinomial_zero_zero : halfQBinomial 0 0 = 1 := by simp

/-- Every positive-index Gaussian coefficient in row zero vanishes. -/
@[simp] theorem halfQBinomial_zero_succ (k : ℕ) :
    halfQBinomial 0 (k + 1) = 0 := by
  exact halfQBinomial_eq_zero_of_lt (by omega)

/-- For `k ≤ n` the coefficient is strictly positive, being a quotient of
positive q-Pochhammer symbols.  This removes the absolute value in
`FabiusDiscreteLimitToeplitz.abs_discreteLimitWeight`. -/
theorem halfQBinomial_pos {n k : ℕ} (hk : k ≤ n) :
    0 < halfQBinomial n k := by
  rw [halfQBinomial_eq_quotient hk]
  exact div_pos (halfQPochhammer_pos n)
    (mul_pos (halfQPochhammer_pos k) (halfQPochhammer_pos (n - k)))

/-- For `k ≤ n` the coefficient is nonzero; the contrapositive direction of
`halfQBinomial_eq_zero_iff`. -/
theorem halfQBinomial_ne_zero {n k : ℕ} (hk : k ≤ n) :
    halfQBinomial n k ≠ 0 := (halfQBinomial_pos hk).ne'

/-- `halfQBinomial n k` vanishes exactly above the diagonal: it is `0` if
and only if `n < k`.  Both directions are proved here, from
`halfQBinomial_ne_zero` and `halfQBinomial_eq_zero_of_lt`. -/
theorem halfQBinomial_eq_zero_iff {n k : ℕ} :
    halfQBinomial n k = 0 ↔ n < k := by
  constructor
  · intro h
    by_contra hnot
    exact (halfQBinomial_ne_zero (Nat.le_of_not_gt hnot)) h
  · exact halfQBinomial_eq_zero_of_lt

/-- Literal `q = 1/2` q-binomial coefficients vanish exactly above the
diagonal. -/
theorem qBinomial_half_eq_zero_iff {n k : ℕ} :
    qBinomial n k (1 / 2) = 0 ↔ n < k := by
  simpa only [qBinomial_half_eq] using
    (halfQBinomial_eq_zero_iff (n := n) (k := k))

private theorem choose_split (n k : ℕ) (hk : k ≤ n) :
    (n + 1).choose 2 =
      (k + 1).choose 2 + k * (n - k) + (n - k + 1).choose 2 := by
  have h := choose_add_succ_two k (n - k)
  rw [Nat.add_sub_of_le hk] at h
  exact h

/-- Mersenne-product normalization of the Gaussian coefficient at `q=1/2`. -/
theorem halfQBinomial_eq_mersenne {n k : ℕ} (hk : k ≤ n) :
    halfQBinomial n k =
      halfMersenneProduct n /
        (halfMersenneProduct k * halfMersenneProduct (n - k) *
          (2 : ℚ) ^ (k * (n - k))) := by
  rw [halfQBinomial_eq_quotient hk]
  simp_rw [halfQPochhammer_eq_mersenne_div]
  rw [choose_split n k hk, pow_add, pow_add]
  field_simp [halfMersenneProduct_ne_zero]

/-- Reflection `k ↦ n - k` for the generic q-Pochhammer quotient: in the
admissible range its two denominator factors merely swap. -/
theorem qBinomial_symm (q : ℚ) {n k : ℕ} (hk : k ≤ n) :
    qBinomial n (n - k) q = qBinomial n k q := by
  rw [qBinomial_eq_quotient q (Nat.sub_le n k),
    qBinomial_eq_quotient q hk, Nat.sub_sub_self hk]
  ring

/-- Reflection `k ↦ n - k` for `k ≤ n`: the quotient is unchanged because
its two denominator factors merely swap.  It supplies the reindexing in
`FabiusDiscreteLimitIntegration.discreteLimit_coefficient_reindex`. -/
theorem halfQBinomial_symm {n k : ℕ} (hk : k ≤ n) :
    halfQBinomial n (n - k) = halfQBinomial n k := by
  simpa only [qBinomial_half_eq] using qBinomial_symm (1 / 2) hk

/-- **The half-base Gaussian coefficient is the quotient coefficient.**
The denominator-free Gaussian coefficient from `FiniteQBinomialCore`
specializes at `q = 1/2` to the established rational half-q coefficient.
The proof is the direct consequence of the full q-factorial identity
`(q;q)_n = (q;q)_k (q;q)_(n-k) [n choose k]_q`
(`finiteQPochhammerIn_self_eq_mul_mul_gaussianBinomial`), divided by the
nonvanishing denominator; above the diagonal both sides vanish.  Both
q-Pascal recurrences of `halfQBinomial` are inherited from the core
through this identification. -/
theorem gaussianBinomial_half_eq_halfQBinomial (n k : ℕ) :
    gaussianBinomial (1 / 2 : ℚ) n k = halfQBinomial n k := by
  by_cases hk : k ≤ n
  · have h := finiteQPochhammerIn_self_eq_mul_mul_gaussianBinomial
      (1 / 2 : ℚ) hk
    change halfQPochhammer n =
      halfQPochhammer k * halfQPochhammer (n - k) *
        gaussianBinomial (1 / 2 : ℚ) n k at h
    rw [halfQBinomial_eq_quotient hk,
      eq_div_iff (mul_ne_zero (halfQPochhammer_ne_zero k)
        (halfQPochhammer_ne_zero (n - k))),
      h]
    ring
  · have hnk : n < k := Nat.lt_of_not_ge hk
    rw [gaussianBinomial_eq_zero_of_lt _ hnk,
      halfQBinomial_eq_zero_of_lt hnk]

/-- The q-Pascal recurrence, in the orientation suited to the finite
q-binomial theorem.  It is the `q = 1/2` instance of the core recurrence
`gaussianBinomial_succ_succ_alt`. -/
theorem halfQBinomial_succ_succ (n k : ℕ) :
    halfQBinomial (n + 1) (k + 1) =
      halfQBinomial n k +
        (1 / 2 : ℚ) ^ (k + 1) * halfQBinomial n (k + 1) := by
  simp only [← gaussianBinomial_half_eq_halfQBinomial]
  rw [gaussianBinomial_succ_succ_alt, add_comm]

/-- The symmetric q-Pascal recurrence, the `q = 1/2` instance of the
core recurrence `gaussianBinomial_succ_succ`. -/
theorem halfQBinomial_succ_succ' (n k : ℕ) :
    halfQBinomial (n + 1) (k + 1) =
      halfQBinomial n (k + 1) +
        (1 / 2 : ℚ) ^ (n - k) * halfQBinomial n k := by
  simp only [← gaussianBinomial_half_eq_halfQBinomial]
  exact gaussianBinomial_succ_succ (1 / 2 : ℚ) n k

/-- The finite q-binomial theorem specialized to `q = 1/2`.  Its proof is
now the direct rational specialization of the denominator-free
commutative-ring theorem. -/
theorem halfQBinomial_theorem (n : ℕ) (z : ℚ) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ (k.choose 2) *
        halfQBinomial n k * z ^ k) =
      finiteQPochhammer z (1 / 2) n := by
  simpa only [gaussianBinomial_half_eq_halfQBinomial,
    finiteQPochhammerIn_rat_eq] using
      finite_qBinomial_theorem (1 / 2 : ℚ) z n

/-- Notation-faithful form of the finite q-binomial theorem at `q = 1/2`. -/
theorem qBinomial_half_theorem (n : ℕ) (z : ℚ) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ (k.choose 2) *
        qBinomial n k (1 / 2) * z ^ k) =
      qPochhammer z (1 / 2) n := by
  simpa only [qBinomial_half_eq] using halfQBinomial_theorem n z

/-- The half-q binomial sum indexed by `n` vanishes exactly at the rational
points `2^j` with `j < n`. -/
theorem halfQBinomial_sum_eq_zero_iff (n : ℕ) (z : ℚ) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ (k.choose 2) *
        halfQBinomial n k * z ^ k) = 0 ↔
      ∃ j < n, z = (2 : ℚ) ^ j := by
  rw [halfQBinomial_theorem n z,
    finiteQPochhammer_half_eq_zero_iff]

/-- Literal `QBinomial[n,k,1/2]` form of the complete rational root locus. -/
theorem qBinomial_half_sum_eq_zero_iff (n : ℕ) (z : ℚ) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ (k.choose 2) *
        qBinomial n k (1 / 2) * z ^ k) = 0 ↔
      ∃ j < n, z = (2 : ℚ) ^ j := by
  simpa only [qBinomial_half_eq] using
    halfQBinomial_sum_eq_zero_iff n z

/-- Scalar extension of the complete rational root locus.  In every field
over `ℚ`, the half-q-binomial sum evaluated at the image of a rational `z`
vanishes exactly when that image is one of the dyadic points `2^j`, `j < n`.
Injectivity of the algebra map shows that scalar extension neither creates
nor loses any rational root. -/
theorem qBinomial_half_sum_algebraMap_eq_zero_iff
    {K : Type*} [Field K] [Algebra ℚ K] (n : ℕ) (z : ℚ) :
    (∑ k ∈ Finset.range (n + 1),
      algebraMap ℚ K
          ((-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ (k.choose 2) *
            qBinomial n k (1 / 2)) *
        (algebraMap ℚ K z) ^ k) = 0 ↔
      ∃ j < n, algebraMap ℚ K z = (2 : K) ^ j := by
  have hsum :
      (∑ k ∈ Finset.range (n + 1),
        algebraMap ℚ K
            ((-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ (k.choose 2) *
              qBinomial n k (1 / 2)) *
          (algebraMap ℚ K z) ^ k) =
        algebraMap ℚ K
          (∑ k ∈ Finset.range (n + 1),
            (-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ (k.choose 2) *
              qBinomial n k (1 / 2) * z ^ k) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    simp only [map_mul, map_pow]
  rw [hsum, map_eq_zero_iff _ (algebraMap ℚ K).injective,
    qBinomial_half_sum_eq_zero_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, by simp only [map_pow, map_ofNat]⟩
  · rintro ⟨j, hj, hz⟩
    refine ⟨j, hj, (algebraMap ℚ K).injective ?_⟩
    simpa only [map_pow, map_ofNat, map_zero, zero_add] using hz

/-! ## Dyadic-node specializations -/

/-- The signed Gaussian weight used by the dyadic interpolation functional:
`(-1)^k (1/2)^(choose k 2) [n choose k]_(1/2)`. -/
noncomputable def halfQBinomialDyadicWeight (n k : ℕ) : ℚ :=
  (-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ k.choose 2 * halfQBinomial n k

/-- The negative dyadic interpolation node `-(2^k)`. -/
def negativeDyadicNode (k : ℕ) : ℚ := -((2 : ℚ) ^ k)

/-- The finite q-binomial theorem evaluated at the dyadic node `z = 2^m`,
with no ordering hypothesis on `m` and `n`.  Keeping the q-Pochhammer value
on the right makes this the common wrapper for both the vanishing nodes
`m < n` and the endpoint `m = n`, while also retaining the values for
`n < m`. -/
theorem halfQBinomial_two_pow_sum_eq_qPochhammer (n m : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ (k.choose 2) *
        halfQBinomial n k * ((2 : ℚ) ^ m) ^ k) =
      qPochhammer ((2 : ℚ) ^ m) (1 / 2) n := by
  exact halfQBinomial_theorem n ((2 : ℚ) ^ m)

/-- Literal `QBinomial[n,k,1/2]` form of the all-index dyadic-node
specialization. -/
theorem qBinomial_half_two_pow_sum_eq_qPochhammer (n m : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ (k.choose 2) *
        qBinomial n k (1 / 2) * ((2 : ℚ) ^ m) ^ k) =
      qPochhammer ((2 : ℚ) ^ m) (1 / 2) n := by
  simpa only [qBinomial_half_eq] using
    halfQBinomial_two_pow_sum_eq_qPochhammer n m

private theorem two_pow_mul_half_pow (n j : ℕ) (hj : j ≤ n) :
    (2 : ℚ) ^ n * (1 / 2 : ℚ) ^ j = (2 : ℚ) ^ (n - j) := by
  rw [div_pow]
  simp only [one_pow]
  have hpow : (2 : ℚ) ^ n = (2 : ℚ) ^ j * (2 : ℚ) ^ (n - j) := by
    rw [← pow_add, Nat.add_sub_of_le hj]
  rw [hpow]
  field_simp

/-- For `m < n` the symbol `(2^m; 1/2)_n` vanishes, since its `j = m` factor
is `1 - 2^m (1/2)^m = 0`.  Fed through the q-binomial theorem this becomes
`halfQBinomial_two_pow_sum_eq_zero`, the vanishing half of the interpolation
data that `FabiusQBinomialFormula` uses at the nodes `-(2^k)`. -/
theorem qPochhammer_two_pow_eq_zero {n m : ℕ} (hm : m < n) :
    qPochhammer ((2 : ℚ) ^ m) (1 / 2) n = 0 := by
  unfold qPochhammer finiteQPochhammer
  apply Finset.prod_eq_zero (i := m)
  · exact Finset.mem_range.mpr hm
  · rw [two_pow_mul_half_pow m m (le_refl m)]
    norm_num

/-- At and beyond the last interpolation node, `(2^m; 1/2)_n` is the signed
quotient of two Mersenne products.  This includes `n = 0` and specializes at
`m = n` to `qPochhammer_two_pow_self_eq_mersenne`. -/
theorem qPochhammer_two_pow_eq_mersenne_div {n m : ℕ} (hnm : n ≤ m) :
    qPochhammer ((2 : ℚ) ^ m) (1 / 2) n =
      (-1 : ℚ) ^ n * halfMersenneProduct m /
        halfMersenneProduct (m - n) := by
  have hterm (j : ℕ) (hj : j < n) :
      1 - (2 : ℚ) ^ m * (1 / 2 : ℚ) ^ j =
        -((2 : ℚ) ^ (m - j) - 1) := by
    rw [two_pow_mul_half_pow m j (hj.le.trans hnm)]
    ring
  have hreflect :
      (∏ j ∈ Finset.range n, ((2 : ℚ) ^ (m - j) - 1)) =
        ∏ j ∈ Finset.range n,
          ((2 : ℚ) ^ ((m - n) + j + 1) - 1) := by
    rw [← Finset.prod_range_reflect
      (fun j => ((2 : ℚ) ^ ((m - n) + j + 1) - 1)) n]
    apply Finset.prod_congr rfl
    intro j hj
    congr 2
    have hjlt := Finset.mem_range.mp hj
    omega
  have hsplit :
      halfMersenneProduct m =
        halfMersenneProduct (m - n) *
          ∏ j ∈ Finset.range n,
            ((2 : ℚ) ^ ((m - n) + j + 1) - 1) := by
    simpa only [Nat.sub_add_cancel hnm] using
      halfMersenneProduct_add (m - n) n
  unfold qPochhammer finiteQPochhammer
  calc
    (∏ j ∈ Finset.range n,
        (1 - (2 : ℚ) ^ m * (1 / 2 : ℚ) ^ j)) =
        ∏ j ∈ Finset.range n, -((2 : ℚ) ^ (m - j) - 1) := by
      apply Finset.prod_congr rfl
      intro j hj
      exact hterm j (Finset.mem_range.mp hj)
    _ = (-1 : ℚ) ^ n *
          ∏ j ∈ Finset.range n, ((2 : ℚ) ^ (m - j) - 1) := by
      calc
        (∏ j ∈ Finset.range n, -((2 : ℚ) ^ (m - j) - 1)) =
            ∏ j ∈ Finset.range n,
              ((-1 : ℚ) * ((2 : ℚ) ^ (m - j) - 1)) := by
          apply Finset.prod_congr rfl
          intro j _hj
          ring
        _ = _ := by
          rw [Finset.prod_mul_distrib]
          simp
    _ = (-1 : ℚ) ^ n *
          ∏ j ∈ Finset.range n,
            ((2 : ℚ) ^ ((m - n) + j + 1) - 1) := by
      rw [hreflect]
    _ = (-1 : ℚ) ^ n * halfMersenneProduct m /
          halfMersenneProduct (m - n) := by
      rw [hsplit]
      field_simp [halfMersenneProduct_ne_zero]

/-- At the endpoint `m = n`, the dyadic q-Pochhammer symbol is the signed
product of the first `n` Mersenne factors.  This division-free form is the
product identity behind `halfQBinomial_two_pow_sum_eq_self`. -/
theorem qPochhammer_two_pow_self_eq_mersenne (n : ℕ) :
    qPochhammer ((2 : ℚ) ^ n) (1 / 2) n =
      (-1 : ℚ) ^ n * halfMersenneProduct n := by
  simpa using qPochhammer_two_pow_eq_mersenne_div (le_refl n)

/-- At and beyond the last interpolation node, the dyadic q-Pochhammer value
is nonzero. -/
theorem qPochhammer_two_pow_ne_zero_of_le {n m : ℕ} (hnm : n ≤ m) :
    qPochhammer ((2 : ℚ) ^ m) (1 / 2) n ≠ 0 := by
  rw [qPochhammer_two_pow_eq_mersenne_div hnm]
  exact div_ne_zero
    (mul_ne_zero (pow_ne_zero n (by norm_num))
      (halfMersenneProduct_ne_zero m))
    (halfMersenneProduct_ne_zero (m - n))

/-- The dyadic q-Pochhammer value vanishes exactly below the last
interpolation node. -/
theorem qPochhammer_two_pow_eq_zero_iff (n m : ℕ) :
    qPochhammer ((2 : ℚ) ^ m) (1 / 2) n = 0 ↔ m < n := by
  constructor
  · intro hzero
    by_contra hnot
    exact qPochhammer_two_pow_ne_zero_of_le (Nat.le_of_not_gt hnot) hzero
  · exact qPochhammer_two_pow_eq_zero

/-- Exact value of `(2^m; 1/2)_n` at every dyadic node: it vanishes below the
last interpolation node and is a signed Mersenne quotient from that node on. -/
theorem qPochhammer_two_pow_eq_ite (n m : ℕ) :
    qPochhammer ((2 : ℚ) ^ m) (1 / 2) n =
      if m < n then 0 else
        (-1 : ℚ) ^ n * halfMersenneProduct m /
          halfMersenneProduct (m - n) := by
  by_cases hmn : m < n
  · rw [if_pos hmn, qPochhammer_two_pow_eq_zero hmn]
  · rw [if_neg hmn]
    exact qPochhammer_two_pow_eq_mersenne_div (Nat.le_of_not_gt hmn)

/-- Closed dyadic-node evaluation of the q-binomial sum at every pair of
indices, combining its vanishing and Mersenne-product regimes. -/
theorem halfQBinomial_two_pow_sum_eq_ite (n m : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ (k.choose 2) *
        halfQBinomial n k * ((2 : ℚ) ^ m) ^ k) =
      if m < n then 0 else
        (-1 : ℚ) ^ n * halfMersenneProduct m /
          halfMersenneProduct (m - n) := by
  rw [halfQBinomial_two_pow_sum_eq_qPochhammer]
  exact qPochhammer_two_pow_eq_ite n m

/-- Literal `QBinomial[n,k,1/2]` form of the closed all-node evaluation. -/
theorem qBinomial_half_two_pow_sum_eq_ite (n m : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ (k.choose 2) *
        qBinomial n k (1 / 2) * ((2 : ℚ) ^ m) ^ k) =
      if m < n then 0 else
        (-1 : ℚ) ^ n * halfMersenneProduct m /
          halfMersenneProduct (m - n) := by
  simpa only [qBinomial_half_eq] using
    halfQBinomial_two_pow_sum_eq_ite n m

/-- The q-binomial dyadic-node sum vanishes exactly below its last
interpolation node. -/
theorem halfQBinomial_two_pow_sum_eq_zero_iff (n m : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ (k.choose 2) *
        halfQBinomial n k * ((2 : ℚ) ^ m) ^ k) = 0 ↔ m < n := by
  rw [halfQBinomial_two_pow_sum_eq_qPochhammer]
  exact qPochhammer_two_pow_eq_zero_iff n m

/-- Literal `QBinomial[n,k,1/2]` form of the exact vanishing criterion. -/
theorem qBinomial_half_two_pow_sum_eq_zero_iff (n m : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ (k.choose 2) *
        qBinomial n k (1 / 2) * ((2 : ℚ) ^ m) ^ k) = 0 ↔ m < n := by
  simpa only [qBinomial_half_eq] using
    halfQBinomial_two_pow_sum_eq_zero_iff n m

/-- The q-binomial sum vanishes at every dyadic node `2^m` with `m < n`. -/
theorem halfQBinomial_two_pow_sum_eq_zero {n m : ℕ} (hm : m < n) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ (k.choose 2) *
        halfQBinomial n k * ((2 : ℚ) ^ m) ^ k) = 0 := by
  rw [halfQBinomial_two_pow_sum_eq_qPochhammer]
  exact qPochhammer_two_pow_eq_zero hm

/-- Evaluation at the last dyadic node. -/
theorem halfQBinomial_two_pow_sum_eq_self (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ (k.choose 2) *
        halfQBinomial n k * ((2 : ℚ) ^ n) ^ k) =
      (-1 : ℚ) ^ n * (2 : ℚ) ^ ((n + 1).choose 2) *
        halfQPochhammer n := by
  rw [halfQBinomial_two_pow_sum_eq_qPochhammer]
  calc
    qPochhammer ((2 : ℚ) ^ n) (1 / 2) n =
        (-1 : ℚ) ^ n * halfMersenneProduct n :=
      qPochhammer_two_pow_self_eq_mersenne n
    _ = (-1 : ℚ) ^ n * (2 : ℚ) ^ ((n + 1).choose 2) *
        halfQPochhammer n := by
      rw [halfQPochhammer_eq_mersenne_div]
      field_simp

/-! ## Gaussian/Prouhet extraction on the negative dyadic nodes -/

/-- A weighted negative-dyadic monomial term is the corresponding positive
dyadic q-binomial term times the common sign `(-1)^d`. -/
theorem halfQBinomialDyadicWeight_mul_negativeDyadicNode_pow
    (n d k : ℕ) :
    halfQBinomialDyadicWeight n k * negativeDyadicNode k ^ d =
      (-1 : ℚ) ^ d *
        ((-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ k.choose 2 *
          halfQBinomial n k * ((2 : ℚ) ^ d) ^ k) := by
  have hp : (((2 : ℚ) ^ k) ^ d) = ((2 : ℚ) ^ d) ^ k := by
    rw [← pow_mul, ← pow_mul, mul_comm]
  unfold halfQBinomialDyadicWeight negativeDyadicNode
  rw [neg_pow ((2 : ℚ) ^ k) d, hp]
  ring

/-- **Field-level node/weight identity.**  In any field, the signed
Gaussian weights `(-1)^k q^(C(k,2)) [n choose k]_q` at the nodes
`-(q⁻¹)^k` have the monomial moments

`∑_{k=0}^n (-1)^k q^(C(k,2)) [n choose k]_q (-(q⁻¹)^k)^d
  = (-1)^d (q^(-d); q)_n`.

This is the finite q-binomial theorem at `z = q^(-d)` after pulling the
sign `(-1)^d` out of every node power.  The specialization `q = 1/2` is
the Gaussian/Prouhet layer of `halfQBinomialDyadicWeight` at the
negative dyadic nodes.  No hypothesis on `q` is needed, since
`0⁻¹ = 0`. -/
theorem sum_gaussianWeight_mul_neg_inv_pow {K : Type*} [Field K]
    (q : K) (n d : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      ((-1 : K) ^ k * q ^ k.choose 2 * gaussianBinomial q n k) *
        (-(q⁻¹) ^ k) ^ d) =
      (-1 : K) ^ d * finiteQPochhammerIn ((q ^ d)⁻¹) q n := by
  rw [← finite_qBinomial_theorem, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  have hpow : ((q⁻¹) ^ k) ^ d = ((q ^ d)⁻¹) ^ k := by
    rw [← inv_pow, ← pow_mul, ← pow_mul, mul_comm]
  rw [neg_pow ((q⁻¹) ^ k) d, hpow]
  ring

/-- **All monomial moments of the negative-dyadic Gaussian functional.**
The `q = 1/2` instance of `sum_gaussianWeight_mul_neg_inv_pow`: for
every degree `d`,

`∑_{k=0}^n halfQBinomialDyadicWeight n k (-(2^k))^d
  = (-1)^d (2^d; 1/2)_n`.

The lower and top moments `halfQBinomialDyadicWeight_nodes_zero` and
`halfQBinomialDyadicWeight_nodes_self` are its evaluations through the
dyadic-node values of `qPochhammer`. -/
theorem halfQBinomialDyadicWeight_nodes_pow (n d : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      halfQBinomialDyadicWeight n k * negativeDyadicNode k ^ d) =
      (-1 : ℚ) ^ d * qPochhammer ((2 : ℚ) ^ d) (1 / 2) n := by
  have h := sum_gaussianWeight_mul_neg_inv_pow (1 / 2 : ℚ) n d
  have hinv : ((1 / 2 : ℚ)⁻¹) = 2 := by norm_num
  have hinvd : (((1 / 2 : ℚ) ^ d)⁻¹) = (2 : ℚ) ^ d := by
    rw [← inv_pow, hinv]
  rw [hinv, hinvd] at h
  simp only [gaussianBinomial_half_eq_halfQBinomial,
    finiteQPochhammerIn_rat_eq] at h
  unfold halfQBinomialDyadicWeight negativeDyadicNode
  exact h

/-- **Lower Gaussian/Prouhet moments.**  The signed half-q-binomial weights
at the nodes `-(2^k)` annihilate every monomial of degree `d < n`. -/
theorem halfQBinomialDyadicWeight_nodes_zero {n d : ℕ} (hd : d < n) :
    (∑ k ∈ Finset.range (n + 1),
      halfQBinomialDyadicWeight n k * negativeDyadicNode k ^ d) = 0 := by
  rw [halfQBinomialDyadicWeight_nodes_pow,
    qPochhammer_two_pow_eq_zero hd, mul_zero]

/-- **Top Gaussian/Prouhet moment.**  At degree `n`, the signed
negative-dyadic functional is the positive exact factor
`2^(choose (n+1) 2) (1/2;1/2)_n`. -/
theorem halfQBinomialDyadicWeight_nodes_self (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      halfQBinomialDyadicWeight n k * negativeDyadicNode k ^ n) =
        (2 : ℚ) ^ ((n + 1).choose 2) * halfQPochhammer n := by
  rw [halfQBinomialDyadicWeight_nodes_pow,
    ← halfQBinomial_two_pow_sum_eq_qPochhammer,
    halfQBinomial_two_pow_sum_eq_self]
  have hsign : (-1 : ℚ) ^ n * (-1 : ℚ) ^ n = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc
    (-1 : ℚ) ^ n *
          ((-1 : ℚ) ^ n * 2 ^ (n + 1).choose 2 * halfQPochhammer n) =
        (((-1 : ℚ) ^ n * (-1 : ℚ) ^ n) *
          2 ^ (n + 1).choose 2) * halfQPochhammer n := by ring
    _ = _ := by rw [hsign, one_mul]

/-- **Degree-valued Gaussian/Prouhet extractor.**  On rational polynomials
of degree at most `n`, the signed half-q-binomial functional at the negative
dyadic nodes extracts the coefficient of degree `n`, multiplied by the exact
top q-Pochhammer moment.  The `Polynomial.degree` hypothesis includes the
zero polynomial uniformly, even when `n = 0`. -/
theorem halfQBinomial_negativeDyadic_polynomial_sum_eq_coeff
    (n : ℕ) (p : Polynomial ℚ) (hp : p.degree ≤ (n : WithBot ℕ)) :
    (∑ k ∈ Finset.range (n + 1),
      halfQBinomialDyadicWeight n k * p.eval (negativeDyadicNode k)) =
        p.coeff n *
          ((2 : ℚ) ^ ((n + 1).choose 2) * halfQPochhammer n) := by
  have hnat : p.natDegree ≤ n :=
    Polynomial.natDegree_le_of_degree_le hp
  have hselect := sum_weight_mul_eval₂_eq_topCoeff_mul_moment
    (RingHom.id ℚ) (Finset.range (n + 1))
    (halfQBinomialDyadicWeight n) negativeDyadicNode
    p n hnat fun _d hd => halfQBinomialDyadicWeight_nodes_zero hd
  rw [halfQBinomialDyadicWeight_nodes_self] at hselect
  simpa only [Polynomial.eval₂_id, RingHom.id_apply] using hselect

/-- Mersenne-product form of the degree-valued Gaussian/Prouhet extractor:
the top moment is exactly `halfMersenneProduct n`. -/
theorem halfQBinomial_negativeDyadic_polynomial_sum_eq_mersenne
    (n : ℕ) (p : Polynomial ℚ) (hp : p.degree ≤ (n : WithBot ℕ)) :
    (∑ k ∈ Finset.range (n + 1),
      halfQBinomialDyadicWeight n k * p.eval (negativeDyadicNode k)) =
        p.coeff n * halfMersenneProduct n := by
  rw [halfQBinomial_negativeDyadic_polynomial_sum_eq_coeff n p hp,
    halfQPochhammer_eq_mersenne_div]
  field_simp

/-- **Strict-degree Gaussian/Prouhet cancellation.**  Every rational
polynomial of degree below `n` is annihilated by the signed half-q-binomial
functional on the negative dyadic nodes.  At the boundary `n = 0`, the
degree hypothesis admits exactly the zero polynomial, so that case is part
of the same statement. -/
theorem halfQBinomial_negativeDyadic_polynomial_sum_eq_zero_of_degree_lt
    (n : ℕ) (p : Polynomial ℚ) (hp : p.degree < (n : WithBot ℕ)) :
    (∑ k ∈ Finset.range (n + 1),
      halfQBinomialDyadicWeight n k * p.eval (negativeDyadicNode k)) = 0 := by
  rw [halfQBinomial_negativeDyadic_polynomial_sum_eq_coeff n p hp.le,
    Polynomial.coeff_eq_zero_of_degree_lt hp, zero_mul]

/-- Literal-notation vanishing form used by the Fabius formula. -/
theorem qBinomial_half_two_pow_sum_eq_zero {n m : ℕ} (hm : m < n) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ (k.choose 2) *
        qBinomial n k (1 / 2) * ((2 : ℚ) ^ m) ^ k) = 0 := by
  simpa only [qBinomial_half_eq] using halfQBinomial_two_pow_sum_eq_zero hm

/-- Literal-notation endpoint evaluation used by the Fabius formula. -/
theorem qBinomial_half_two_pow_sum_eq_self (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ (k.choose 2) *
        qBinomial n k (1 / 2) * ((2 : ℚ) ^ n) ^ k) =
      (-1 : ℚ) ^ n * (2 : ℚ) ^ ((n + 1).choose 2) *
        qPochhammer (1 / 2) (1 / 2) n := by
  simpa only [qBinomial_half_eq, qPochhammer_half_eq] using
    halfQBinomial_two_pow_sum_eq_self n

end Fabius
