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
* `qBinomial`, `halfQBinomial`, `halfQBinomial_pos`, `halfQBinomial_symm`,
  `halfQBinomial_succ_succ`, `halfQBinomial_succ_succ'` -- the coefficient,
  positivity for `k ≤ n`, the reflection `k ↦ n - k`, and both orientations
  of the q-Pascal recurrence.
* `halfQBinomial_theorem` -- the q-binomial theorem displayed above.
* `finiteQPochhammer_eq_zero_iff`,
  `finiteQPochhammer_half_eq_zero_iff`,
  `halfQBinomial_sum_eq_zero_iff`, and
  `qBinomial_half_sum_eq_zero_iff` -- the general product-zero criterion and
  the complete rational root locus `2^j` for `j < n` at `q = 1/2`.
* `qBinomial_half_sum_algebraMap_eq_zero_iff` -- the same root locus after
  embedding the rational argument and coefficients in an arbitrary field
  over `ℚ`.
* `halfQBinomial_two_pow_sum_eq_qPochhammer` -- the all-index dyadic-node
  specialization, with an exact piecewise Mersenne-product form and the
  existing zero/endpoint interpolation boundaries.
* `halfQBinomialDyadicWeight`, `negativeDyadicNode`,
  `halfQBinomialDyadicWeight_nodes_zero`, and
  `halfQBinomialDyadicWeight_nodes_self` -- the signed Gaussian weights,
  their negative dyadic nodes, and the lower/top monomial moments.
* `halfQBinomial_negativeDyadic_polynomial_sum_eq_coeff` -- the
  degree-valued Gaussian/Prouhet extractor, including the zero-polynomial
  boundary, with q-Pochhammer and Mersenne-product right-hand sides.
* `qPochhammer_two_pow_eq_mersenne_div` and `qPochhammer_two_pow_eq_ite` --
  the closed Mersenne-product value at every dyadic node.
* `four_pow_choose_two` -- `4^(C(k,2)) = 2^(k(k-1))`, which rewrites the
  Wolfram denominator as a pure power of two.

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
root-locus theorems classify rational arguments, while the scalar-extension
form classifies their images in fields over `ℚ`; these results do not yet
classify arbitrary scalar arguments or package root multiplicities.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

/-- The finite Wolfram-language `QPochhammer[a,q,n]`, over `ℚ`. -/
noncomputable def finiteQPochhammer (a q : ℚ) (n : ℕ) : ℚ :=
  ∏ j ∈ Finset.range n, (1 - a * q ^ j)

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

@[simp] theorem qPochhammer_zero (a q : ℚ) : qPochhammer a q 0 = 1 := by
  exact finiteQPochhammer_zero a q

/-- The same top-factor recurrence stated for the Wolfram alias, so that
statements written in literal `QPochhammer` notation never have to unfold to
`finiteQPochhammer`. -/
theorem qPochhammer_succ (a q : ℚ) (n : ℕ) :
    qPochhammer a q (n + 1) =
      qPochhammer a q n * (1 - a * q ^ n) :=
  finiteQPochhammer_succ a q n

/-- A finite q-Pochhammer product vanishes exactly when one of its factors
vanishes.  No nonzero or positivity hypothesis on `q` is needed. -/
theorem finiteQPochhammer_eq_zero_iff (a q : ℚ) (n : ℕ) :
    finiteQPochhammer a q n = 0 ↔
      ∃ j < n, a * q ^ j = 1 := by
  unfold finiteQPochhammer
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨j, hj, hzero⟩
    exact ⟨j, Finset.mem_range.mp hj, (sub_eq_zero.mp hzero).symm⟩
  · rintro ⟨j, hj, hone⟩
    exact ⟨j, Finset.mem_range.mpr hj, sub_eq_zero.mpr hone.symm⟩

private theorem mul_half_pow_eq_one_iff (z : ℚ) (j : ℕ) :
    z * (1 / 2 : ℚ) ^ j = 1 ↔ z = (2 : ℚ) ^ j := by
  constructor
  · intro h
    apply mul_right_cancel₀ (pow_ne_zero j (by norm_num : (1 / 2 : ℚ) ≠ 0))
    rw [h, ← mul_pow]
    norm_num
  · rintro rfl
    rw [← mul_pow]
    norm_num

/-- At `q = 1/2`, the finite q-Pochhammer product vanishes at exactly the
rational points `2^j` with `j < n`. -/
theorem finiteQPochhammer_half_eq_zero_iff (z : ℚ) (n : ℕ) :
    finiteQPochhammer z (1 / 2) n = 0 ↔
      ∃ j < n, z = (2 : ℚ) ^ j := by
  rw [finiteQPochhammer_eq_zero_iff]
  constructor
  · rintro ⟨j, hj, hterm⟩
    exact ⟨j, hj, (mul_half_pow_eq_one_iff z j).1 hterm⟩
  · rintro ⟨j, hj, hz⟩
    exact ⟨j, hj, (mul_half_pow_eq_one_iff z j).2 hz⟩

/-- The specialization `QPochhammer[1/2,1/2,n]`. -/
noncomputable def halfQPochhammer (n : ℕ) : ℚ :=
  finiteQPochhammer (1 / 2) (1 / 2) n

@[simp] theorem qPochhammer_half_eq (n : ℕ) :
    qPochhammer (1 / 2) (1 / 2) n = halfQPochhammer n := by
  rfl

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

/-- The Wolfram denominator `4^Binomial[k,2]` as a pure power of two. -/
theorem four_pow_choose_two (k : ℕ) :
    (4 : ℚ) ^ (k.choose 2) = (2 : ℚ) ^ (k * (k - 1)) := by
  have htwo : 2 * k.choose 2 = k * (k - 1) := by
    cases k with
    | zero => simp
    | succ k =>
        simpa [mul_comm] using two_mul_choose_succ_two k
  calc
    (4 : ℚ) ^ (k.choose 2) = ((2 : ℚ) ^ 2) ^ (k.choose 2) := by norm_num
    _ = (2 : ℚ) ^ (2 * k.choose 2) := by rw [pow_mul]
    _ = (2 : ℚ) ^ (k * (k - 1)) := by rw [htwo]

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

/-- In the admissible range `k ≤ n` the `if` unfolds and `halfQBinomial n k`
is the q-Pochhammer quotient
`(1/2;1/2)_n / ((1/2;1/2)_k (1/2;1/2)_(n-k))`.  The hypothesis `k ≤ n` is
needed because `n - k` is truncated natural subtraction.  Every quotient
manipulation below starts from this rewrite. -/
theorem halfQBinomial_eq_quotient {n k : ℕ} (hk : k ≤ n) :
    halfQBinomial n k =
      halfQPochhammer n /
        (halfQPochhammer k * halfQPochhammer (n - k)) := by
  simp [halfQBinomial, hk]

/-- The coefficient vanishes above the diagonal, `n < k`.  This is what
kills the extra term when a sum over `range (n + 1)` is compared with a sum
over `range (n + 2)` in the induction proving `halfQBinomial_theorem`. -/
theorem halfQBinomial_eq_zero_of_lt {n k : ℕ} (hk : n < k) :
    halfQBinomial n k = 0 := by
  simp [halfQBinomial, Nat.not_le.mpr hk]

@[simp] theorem halfQBinomial_zero_right (n : ℕ) :
    halfQBinomial n 0 = 1 := by
  rw [halfQBinomial_eq_quotient (Nat.zero_le n)]
  simp [halfQPochhammer_ne_zero]

@[simp] theorem halfQBinomial_self (n : ℕ) :
    halfQBinomial n n = 1 := by
  rw [halfQBinomial_eq_quotient (le_refl n)]
  simp [halfQPochhammer_ne_zero]

@[simp] theorem halfQBinomial_zero_zero : halfQBinomial 0 0 = 1 := by simp

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

/-- Reflection `k ↦ n - k` for `k ≤ n`: the quotient is unchanged because
its two denominator factors merely swap.  It supplies the reindexing in
`FabiusDiscreteLimitIntegration.discreteLimit_coefficient_reindex` and turns
`halfQBinomial_succ_succ` into its symmetric partner
`halfQBinomial_succ_succ'`. -/
theorem halfQBinomial_symm {n k : ℕ} (hk : k ≤ n) :
    halfQBinomial n (n - k) = halfQBinomial n k := by
  rw [halfQBinomial_eq_quotient (Nat.sub_le n k),
    halfQBinomial_eq_quotient hk]
  rw [Nat.sub_sub_self hk]
  ring

/-- The q-Pascal recurrence, in the orientation suited to the finite
q-binomial theorem. -/
theorem halfQBinomial_succ_succ (n k : ℕ) :
    halfQBinomial (n + 1) (k + 1) =
      halfQBinomial n k +
        (1 / 2 : ℚ) ^ (k + 1) * halfQBinomial n (k + 1) := by
  by_cases hkn : k < n
  · have hk1n1 : k + 1 ≤ n + 1 := by omega
    have hknle : k ≤ n := hkn.le
    have hk1n : k + 1 ≤ n := hkn
    rw [halfQBinomial_eq_quotient hk1n1,
      halfQBinomial_eq_quotient hknle,
      halfQBinomial_eq_quotient hk1n]
    have hsub : n - k = (n - (k + 1)) + 1 := by omega
    have hpow : (1 / 2 : ℚ) ^ (n + 1) =
        (1 / 2 : ℚ) ^ (k + 1) * (1 / 2 : ℚ) ^ (n - k) := by
      rw [← pow_add]
      congr 1
      omega
    have hkfactor : 1 - (1 / 2 : ℚ) ^ (k + 1) ≠ 0 := by
      have hlt := pow_lt_one₀ (a := (1 / 2 : ℚ)) (by norm_num) (by norm_num)
        (by omega : k + 1 ≠ 0)
      linarith
    have hnfactor : 1 - (1 / 2 : ℚ) ^ (n - k) ≠ 0 := by
      have hlt := pow_lt_one₀ (a := (1 / 2 : ℚ)) (by norm_num) (by norm_num)
        (by omega : n - k ≠ 0)
      linarith
    have hpowSub : (1 / 2 : ℚ) ^ (n - k) =
        (1 / 2 : ℚ) ^ (n - (k + 1)) * (1 / 2 : ℚ) := by
      rw [hsub, pow_succ]
    have hnfactor' :
        1 + (1 / 2 : ℚ) ^ (n - (1 + k)) * (-1 / 2) ≠ 0 := by
      have heq : 1 + (1 / 2 : ℚ) ^ (n - (1 + k)) * (-1 / 2) =
          1 - (1 / 2 : ℚ) ^ (n - k) := by
        rw [show 1 + k = k + 1 by omega]
        rw [hpowSub]
        ring
      rw [heq]
      exact hnfactor
    have hden : 1 - (1 / 2 : ℚ) ^ (n - (k + 1) + 1) ≠ 0 := by
      rw [← hsub]
      exact hnfactor
    rw [show n + 1 - (k + 1) = n - k by omega]
    rw [halfQPochhammer_succ n, halfQPochhammer_succ k]
    rw [hsub, halfQPochhammer_succ]
    rw [hpow]
    field_simp [halfQPochhammer_ne_zero, hkfactor, hnfactor, hnfactor']
    rw [hpowSub]
    field_simp [hden]
    ring
  · have hnk : n ≤ k := Nat.le_of_not_gt hkn
    rcases hnk.eq_or_lt with rfl | hnk
    · rw [halfQBinomial_self, halfQBinomial_self,
        halfQBinomial_eq_zero_of_lt (Nat.lt_succ_self n)]
      ring
    · rw [halfQBinomial_eq_zero_of_lt (by omega),
        halfQBinomial_eq_zero_of_lt hnk,
        halfQBinomial_eq_zero_of_lt (by omega)]
      ring

/-- The symmetric q-Pascal recurrence. -/
theorem halfQBinomial_succ_succ' (n k : ℕ) :
    halfQBinomial (n + 1) (k + 1) =
      halfQBinomial n (k + 1) +
        (1 / 2 : ℚ) ^ (n - k) * halfQBinomial n k := by
  by_cases hkn : k < n
  · have hk1n : k + 1 ≤ n := hkn
    have hk1n1 : k + 1 ≤ n + 1 := by omega
    calc
      halfQBinomial (n + 1) (k + 1) =
          halfQBinomial (n + 1) ((n + 1) - (k + 1)) :=
        (halfQBinomial_symm hk1n1).symm
      _ = halfQBinomial (n + 1) (n - k) := by
        rw [show (n + 1) - (k + 1) = n - k by omega]
      _ = halfQBinomial (n + 1) ((n - (k + 1)) + 1) := by
        rw [show n - k = (n - (k + 1)) + 1 by omega]
      _ = halfQBinomial n (n - (k + 1)) +
          (1 / 2 : ℚ) ^ ((n - (k + 1)) + 1) *
            halfQBinomial n ((n - (k + 1)) + 1) :=
        halfQBinomial_succ_succ n (n - (k + 1))
      _ = halfQBinomial n (k + 1) +
          (1 / 2 : ℚ) ^ (n - k) * halfQBinomial n k := by
        rw [show n - (k + 1) = n - (k + 1) by rfl]
        rw [halfQBinomial_symm hk1n]
        rw [show n - (k + 1) + 1 = n - k by omega]
        rw [halfQBinomial_symm hkn.le]
  · have hnk : n ≤ k := Nat.le_of_not_gt hkn
    rcases hnk.eq_or_lt with rfl | hnk
    · rw [halfQBinomial_self,
        halfQBinomial_eq_zero_of_lt (Nat.lt_succ_self n),
        halfQBinomial_self]
      simp
    · rw [halfQBinomial_eq_zero_of_lt (by omega),
        halfQBinomial_eq_zero_of_lt (by omega),
        halfQBinomial_eq_zero_of_lt hnk]
      ring

private noncomputable def halfQBinomialSummand (n : ℕ) (z : ℚ) (k : ℕ) : ℚ :=
  (-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ (k.choose 2) *
    halfQBinomial n k * z ^ k

@[simp] private theorem halfQBinomialSummand_zero (n : ℕ) (z : ℚ) :
    halfQBinomialSummand n z 0 = 1 := by
  simp [halfQBinomialSummand]

private theorem halfQBinomialSummand_succ_succ
    (n k : ℕ) (hk : k ≤ n) (z : ℚ) :
    halfQBinomialSummand (n + 1) z (k + 1) =
      halfQBinomialSummand n z (k + 1) -
        z * (1 / 2 : ℚ) ^ n * halfQBinomialSummand n z k := by
  rw [halfQBinomialSummand, halfQBinomialSummand,
    halfQBinomialSummand, halfQBinomial_succ_succ']
  rw [choose_succ_two, pow_add, pow_succ, pow_succ]
  have hsum : k + (n - k) = n := Nat.add_sub_of_le hk
  have hknpow : (1 / 2 : ℚ) ^ k * (1 / 2 : ℚ) ^ (n - k) =
      (1 / 2 : ℚ) ^ n := by
    rw [← pow_add, hsum]
  ring_nf
  linear_combination
    -(halfQBinomial n k * z * z ^ k * (-1 : ℚ) ^ k *
      (1 / 2 : ℚ) ^ (k.choose 2)) * hknpow

private theorem halfQBinomialSummand_above (n : ℕ) (z : ℚ) :
    halfQBinomialSummand n z (n + 1) = 0 := by
  rw [halfQBinomialSummand, halfQBinomial_eq_zero_of_lt (Nat.lt_succ_self n)]
  ring

/-- The finite q-binomial theorem specialized to `q = 1/2`. -/
theorem halfQBinomial_theorem (n : ℕ) (z : ℚ) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ (k.choose 2) *
        halfQBinomial n k * z ^ k) =
      finiteQPochhammer z (1 / 2) n := by
  change (∑ k ∈ Finset.range (n + 1), halfQBinomialSummand n z k) = _
  induction n with
  | zero => simp [finiteQPochhammer]
  | succ n ih =>
      have hrec :
          (∑ k ∈ Finset.range (n + 1),
              halfQBinomialSummand (n + 1) z (k + 1)) =
            ∑ k ∈ Finset.range (n + 1),
              (halfQBinomialSummand n z (k + 1) -
                z * (1 / 2 : ℚ) ^ n * halfQBinomialSummand n z k) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact halfQBinomialSummand_succ_succ n k
          (by simpa using Finset.mem_range.mp hk) z
      have htail :
          1 + (∑ k ∈ Finset.range (n + 1),
              halfQBinomialSummand n z (k + 1)) =
            ∑ k ∈ Finset.range (n + 1), halfQBinomialSummand n z k := by
        calc
          1 + (∑ k ∈ Finset.range (n + 1),
              halfQBinomialSummand n z (k + 1)) =
              ∑ k ∈ Finset.range (n + 2), halfQBinomialSummand n z k := by
            have hs := (Finset.sum_range_succ'
              (fun k => halfQBinomialSummand n z k) (n + 1)).symm
            rw [show n + 1 + 1 = n + 2 by omega] at hs
            simpa [add_comm] using hs
          _ = (∑ k ∈ Finset.range (n + 1), halfQBinomialSummand n z k) +
                halfQBinomialSummand n z (n + 1) := by
            exact Finset.sum_range_succ _ _
          _ = _ := by rw [halfQBinomialSummand_above, add_zero]
      rw [show n + 1 + 1 = n + 2 by omega, Finset.sum_range_succ']
      rw [halfQBinomialSummand_zero, hrec, Finset.sum_sub_distrib]
      rw [← Finset.mul_sum]
      calc
        (∑ x ∈ Finset.range (n + 1), halfQBinomialSummand n z (x + 1)) -
              z * (1 / 2 : ℚ) ^ n *
                (∑ i ∈ Finset.range (n + 1), halfQBinomialSummand n z i) + 1 =
            (1 + ∑ x ∈ Finset.range (n + 1),
                halfQBinomialSummand n z (x + 1)) -
              z * (1 / 2 : ℚ) ^ n *
                (∑ i ∈ Finset.range (n + 1), halfQBinomialSummand n z i) := by
          ring
        _ = (∑ i ∈ Finset.range (n + 1), halfQBinomialSummand n z i) -
              z * (1 / 2 : ℚ) ^ n *
                (∑ i ∈ Finset.range (n + 1), halfQBinomialSummand n z i) := by
          rw [htail]
        _ = (1 - z * (1 / 2 : ℚ) ^ n) *
              (∑ i ∈ Finset.range (n + 1), halfQBinomialSummand n z i) := by
          ring
        _ = finiteQPochhammer z (1 / 2) (n + 1) := by
          rw [ih, finiteQPochhammer_succ]
          ring

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
    simpa only [map_pow, map_ofNat] using hz

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

/-- **Lower Gaussian/Prouhet moments.**  The signed half-q-binomial weights
at the nodes `-(2^k)` annihilate every monomial of degree `d < n`. -/
theorem halfQBinomialDyadicWeight_nodes_zero {n d : ℕ} (hd : d < n) :
    (∑ k ∈ Finset.range (n + 1),
      halfQBinomialDyadicWeight n k * negativeDyadicNode k ^ d) = 0 := by
  calc
    (∑ k ∈ Finset.range (n + 1),
        halfQBinomialDyadicWeight n k * negativeDyadicNode k ^ d) =
        (-1 : ℚ) ^ d *
          ∑ k ∈ Finset.range (n + 1),
            (-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ k.choose 2 *
              halfQBinomial n k * ((2 : ℚ) ^ d) ^ k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      exact halfQBinomialDyadicWeight_mul_negativeDyadicNode_pow n d k
    _ = 0 := by rw [halfQBinomial_two_pow_sum_eq_zero hd, mul_zero]

/-- **Top Gaussian/Prouhet moment.**  At degree `n`, the signed
negative-dyadic functional is the positive exact factor
`2^(choose (n+1) 2) (1/2;1/2)_n`. -/
theorem halfQBinomialDyadicWeight_nodes_self (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      halfQBinomialDyadicWeight n k * negativeDyadicNode k ^ n) =
        (2 : ℚ) ^ ((n + 1).choose 2) * halfQPochhammer n := by
  calc
    (∑ k ∈ Finset.range (n + 1),
        halfQBinomialDyadicWeight n k * negativeDyadicNode k ^ n) =
        (-1 : ℚ) ^ n *
          ∑ k ∈ Finset.range (n + 1),
            (-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ k.choose 2 *
              halfQBinomial n k * ((2 : ℚ) ^ n) ^ k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      exact halfQBinomialDyadicWeight_mul_negativeDyadicNode_pow n n k
    _ = (2 : ℚ) ^ ((n + 1).choose 2) * halfQPochhammer n := by
      rw [halfQBinomial_two_pow_sum_eq_self]
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
  classical
  have hnat : p.natDegree ≤ n :=
    Polynomial.natDegree_le_of_degree_le hp
  simp_rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hexpand :
      (∑ d ∈ p.support, ∑ k ∈ Finset.range (n + 1),
          halfQBinomialDyadicWeight n k *
            (p.coeff d * negativeDyadicNode k ^ d)) =
        ∑ d ∈ p.support, p.coeff d *
          ∑ k ∈ Finset.range (n + 1),
            halfQBinomialDyadicWeight n k * negativeDyadicNode k ^ d := by
    apply Finset.sum_congr rfl
    intro d _hd
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    ring
  rw [hexpand]
  by_cases hn : n ∈ p.support
  · rw [Finset.sum_eq_single n]
    · rw [halfQBinomialDyadicWeight_nodes_self]
    · intro d hd hdn
      have hdn' : d < n :=
        lt_of_le_of_ne
          (Polynomial.le_natDegree_of_mem_supp d hd |>.trans hnat) hdn
      rw [halfQBinomialDyadicWeight_nodes_zero hdn', mul_zero]
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
    rw [halfQBinomialDyadicWeight_nodes_zero hdn', mul_zero]

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
