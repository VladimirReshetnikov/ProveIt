import FabiusFunction.BitPositionQBinomial
import FabiusFunction.CyclotomicDivisibility
import FabiusFunction.GaussianBinomialAtOne
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Data.Nat.Choose.Dvd

/-!
# The `q`-Babbage congruence modulo a cyclotomic square

For integers `a, b ≥ 0` and `n ≥ 1`,

`[an, bn]_q ≡ [a, b]_{q^{n²}}  (mod Φ_n(q)²)`.

The proof splits the Gauss product `∏_{j < an} (1 + x qʲ)` into `a` consecutive blocks of
length `n` and expands each block by Gauss's binomial formula,

`∏_{j < n} (1 + x q^{in+j}) = (1 + q^{C(n,2) + in²} xⁿ) + E_i`,   `E_i := ∑_{0 < k < n} …`,

where the *extreme* part keeps only `k ∈ {0, n}` and the *error* `E_i` collects the
intermediate terms `0 < k < n`.  Two facts drive everything:

* every coefficient of `E_i` sits in a degree **not** divisible by `n`;
* every coefficient of `E_i` is divisible by `φ`, whenever `φ` divides `[n,k]_q` for all
  `0 < k < n` (for `q = X` over an integral domain one may take `φ = Φ_n`, because the
  exponent of `Φ_n` in the cyclotomic factorization of `[n,k]_X` is `1` there).

Multiplying the blocks and carrying the invariant

`∏_{j < an} (1 + x qʲ) = ∏_{i < a} (1 + q^{C(n,2)+in²} xⁿ) + H + E`,
`H` supported off multiples of `n` and divisible by `φ`,  `E` divisible by `φ²`,

as an induction on `a` reorganises the monograph's "nontrivial block choices occur in
pairs" argument into a statement that never has to reason about multi-indices.  Reading
off the coefficient of `x^{bn}` kills `H` outright and leaves `E` as a multiple of `φ²`.

Two departures from the source text are deliberate.

* The engine has nothing to do with cyclotomic polynomials: it is stated for an
  **arbitrary commutative ring** `R` and arbitrary `q φ : R` in
  `sq_dvd_pow_mul_gaussianBinomial_sub`.  The `q`-Babbage congruence is the case
  `R = ℤ[X]`, `q = X`, `φ = Φ_n`; the **classical Babbage congruence**
  `C(ap, bp) ≡ C(a, b) (mod p²)` is the case `R = ℤ`, `q = 1`, `n = p`, `φ = p`, and is
  obtained here for free as `choose_mul_prime_congr`.
* The hypothesis `a ≥ b` of the source statement is dropped: for `b > a` both Gaussian
  coefficients vanish and the congruence is trivially true.

The generic form is stated with the monomial `q^{C(bn,2)}` still attached, because in
`R` that monomial need not be cancellable.  Over `ℤ[X]` it *is* removable, and that step —
which the source text performs silently — is paid for by `isCoprime_X_cyclotomic`:
`Φ_n(0) = ±1`, so `X` is a unit modulo `Φ_n(X)²`.

The corollary at a primitive `n`-th root of unity is factored through the purely
algebraic `dvd_derivative_of_sq_dvd` (`p² ∣ f → p ∣ f'`), valid over every commutative
ring, rather than through an analytic "zero of order at least two" argument; the
derivative clause is therefore true in positive characteristic as well.

## Main declarations

* `choose_two_mul` — `C(bn, 2) = b·C(n,2) + n²·C(b,2)`, the exponent bookkeeping.
* `sq_dvd_pow_mul_gaussianBinomial_sub` — the generic congruence over any commutative
  ring: `φ² ∣ q^{C(bn,2)} · ([an,bn]_q - [a,b]_{q^{n²}})`.
* `cyclotomic_dvd_gaussianBinomial_of_lt` — `Φ_n ∣ [n,k]_X` for `0 < k < n`, over every
  integral domain (the source cites the carry criterion, which the corpus has only
  over `ℚ`; this is the one-directional statement re-derived in full generality).
* `isCoprime_X_cyclotomic` — `X` and `Φ_n` are coprime in `R[X]`.
* `gaussianBinomial_q_babbage` — the `q`-Babbage congruence in `R[X]` over every integral
  domain, `gaussianBinomial_q_babbage_int` its `ℤ[X]` face (the form the source states),
  and `gaussianBinomial_q_babbage_map` the same congruence transported along
  `Polynomial.map` to `R[X]` for every commutative ring `R`.
* `choose_mul_prime_congr` — the classical Babbage congruence, a specialization.
* `dvd_derivative_of_sq_dvd`, `cyclotomic_dvd_derivative_gaussianBinomial_sub` — the
  derivative half of the corollary before evaluation.
* `gaussianBinomial_mul_isPrimitiveRoot_of_babbage` — the value clause `[an,bn]_ζ = C(a,b)`
  re-derived from the congruence (the corpus already has it from `q`-Lucas as
  `gaussianBinomial_mul_isPrimitiveRoot`; the source says either route works).
* `eval_derivative_gaussianBinomial_mul_isPrimitiveRoot` — the derivative clause: the two
  sides of the congruence have equal derivatives at `q = ζ`.

## What is not covered

No refinement modulo `Φ_n³` (the `q`-Ljunggren congruences of Straub), and no closed form
for the common value of the two derivatives at `q = ζ`: that needs the derivative of
`[a,b]_q` at `q = 1`, which is not in the corpus.  The cyclic sieving statement that
accompanies this section in the source is untouched.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Polynomial Finset

/-! ## Exponent bookkeeping -/

/-- `C(bn, 2) = b·C(n,2) + n²·C(b,2)`: the triangular number of a multiple, split into
the `b` within-block contributions and the `C(b,2)` cross-block ones. -/
theorem choose_two_mul (b n : ℕ) : (b * n).choose 2 = b * n.choose 2 + n ^ 2 * b.choose 2 := by
  induction b with
  | zero =>
      have hc0 : Nat.choose 0 2 = 0 := rfl
      simp [hc0]
  | succ b ih =>
      have h1 : (b + 1) * n = b * n + n := add_one_mul b n
      have h2 : (b + 1).choose 2 = b.choose 2 + b := by
        have h := choose_two_add b 1
        have hc1 : Nat.choose 1 2 = 0 := rfl
        omega
      rw [h1, choose_two_add (b * n) n, ih, h2]
      ring

/-! ## Support calculus for coefficients in arithmetic progressions -/

/-- If neither factor has a coefficient in a degree divisible by `n`, then neither does the
product. -/
private theorem coeff_mul_eq_zero_of_not_dvd {R : Type*} [CommRing R] {n : ℕ} {p r : R[X]}
    (hp : ∀ k, ¬ n ∣ k → p.coeff k = 0) (hr : ∀ k, ¬ n ∣ k → r.coeff k = 0)
    (k : ℕ) (hk : ¬ n ∣ k) : (p * r).coeff k = 0 := by
  rw [Polynomial.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.mem_antidiagonal] at hx
  by_cases h1 : n ∣ x.1
  · have h2 : ¬ n ∣ x.2 := by
      intro h2
      exact hk (by rw [← hx]; exact dvd_add h1 h2)
    rw [hr _ h2, mul_zero]
  · rw [hp _ h1, zero_mul]

/-- If the left factor has no coefficient in a degree divisible by `n`, and the right factor
has *only* such coefficients, then the product has none in any degree divisible by `n`. -/
private theorem coeff_mul_eq_zero_of_dvd {R : Type*} [CommRing R] {n : ℕ} {p r : R[X]}
    (hp : ∀ k, ¬ n ∣ k → p.coeff k = 0) (hr : ∀ k, n ∣ k → r.coeff k = 0)
    (k : ℕ) (hk : n ∣ k) : (p * r).coeff k = 0 := by
  rw [Polynomial.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.mem_antidiagonal] at hx
  by_cases h1 : n ∣ x.1
  · have h2 : n ∣ x.2 := by
      have h3 := Nat.dvd_sub hk h1
      rwa [show k - x.1 = x.2 by omega] at h3
    rw [hr _ h2, mul_zero]
  · rw [hp _ h1, zero_mul]

/-! ## The two halves of a length-`n` block -/

/-- The **extreme part** of the `i`-th length-`n` block: the terms `k = 0` and `k = n` of
Gauss's expansion of `∏_{j<n} (1 + x q^{in+j})`. -/
private noncomputable def babbageBlockMain {R : Type*} [CommRing R] (q : R) (n i : ℕ) : R[X] :=
  1 + C (q ^ (n.choose 2 + i * n ^ 2)) * X ^ n

/-- The **intermediate part** of the `i`-th length-`n` block: the terms `0 < k < n`. -/
private noncomputable def babbageBlockError {R : Type*} [CommRing R] (q : R) (n i : ℕ) : R[X] :=
  ∑ k ∈ range (n - 1),
    C (q ^ ((k + 1).choose 2 + i * n * (k + 1)) * gaussianBinomial q n (k + 1)) * X ^ (k + 1)

/-- The extreme part is supported in degrees `0` and `n`, both multiples of `n`. -/
private theorem coeff_babbageBlockMain_eq_zero {R : Type*} [CommRing R] (q : R) (n i : ℕ) :
    ∀ k, ¬ n ∣ k → (babbageBlockMain q n i).coeff k = 0 := by
  intro k hk
  have hk0 : k ≠ 0 := by rintro rfl; exact hk (dvd_zero n)
  have hkn : k ≠ n := by rintro rfl; exact hk dvd_rfl
  unfold babbageBlockMain
  rw [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_C_mul_X_pow, if_neg hk0,
    if_neg hkn, add_zero]

/-- A product of extreme parts is still supported in degrees divisible by `n`. -/
private theorem coeff_prod_babbageBlockMain_eq_zero {R : Type*} [CommRing R] (q : R) (n a : ℕ) :
    ∀ k, ¬ n ∣ k → (∏ i ∈ range a, babbageBlockMain q n i).coeff k = 0 := by
  induction a with
  | zero =>
      intro k hk
      have hk0 : k ≠ 0 := by rintro rfl; exact hk (dvd_zero n)
      rw [Finset.prod_range_zero, Polynomial.coeff_one, if_neg hk0]
  | succ a ih =>
      intro k hk
      rw [Finset.prod_range_succ]
      exact coeff_mul_eq_zero_of_not_dvd ih (coeff_babbageBlockMain_eq_zero q n a) k hk

/-- The intermediate part is supported in degrees `0 < k < n`, none of them a multiple
of `n`. -/
private theorem coeff_babbageBlockError_eq_zero {R : Type*} [CommRing R] (q : R) (n i : ℕ) :
    ∀ k, n ∣ k → (babbageBlockError q n i).coeff k = 0 := by
  intro k hk
  unfold babbageBlockError
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [Finset.mem_range] at hj
  have hj1 : j + 1 < n := by omega
  have hne : k ≠ j + 1 := by
    intro hkj
    have hle : n ≤ k := Nat.le_of_dvd (by omega) hk
    omega
  rw [Polynomial.coeff_C_mul_X_pow, if_neg hne]

/-- Every coefficient of the intermediate part is divisible by `φ`, as soon as `φ` divides
each interior Gaussian coefficient `[n,k]_q`. -/
private theorem C_dvd_babbageBlockError {R : Type*} [CommRing R] (q φ : R) {n : ℕ}
    (hφ : ∀ k, 0 < k → k < n → φ ∣ gaussianBinomial q n k) (i : ℕ) :
    (C φ : R[X]) ∣ babbageBlockError q n i := by
  unfold babbageBlockError
  refine Finset.dvd_sum fun k hk => ?_
  rw [Finset.mem_range] at hk
  have h1 : φ ∣ gaussianBinomial q n (k + 1) := hφ (k + 1) (by omega) (by omega)
  have h2 : (C φ : R[X]) ∣ C (gaussianBinomial q n (k + 1)) := _root_.map_dvd C h1
  rw [Polynomial.C_mul]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h2 _) _

/-! ## Gauss's formula on a single block -/

/-- Gauss's binomial formula applied to the `i`-th length-`n` block. -/
private theorem prod_range_block_eq {R : Type*} [CommRing R] (q : R) (n i : ℕ) :
    (∏ j ∈ range n, ((1 : R[X]) + X * C (q ^ (i * n + j)))) =
      ∑ k ∈ range (n + 1),
        C (q ^ (k.choose 2 + i * n * k) * gaussianBinomial q n k) * X ^ k := by
  have hfac : ∀ j : ℕ, ((1 : R[X]) + X * C (q ^ (i * n + j))) =
      1 + (X * C (q ^ (i * n))) * (C q : R[X]) ^ j := by
    intro j
    have hC : (C (q ^ (i * n + j)) : R[X]) = C (q ^ (i * n)) * (C q : R[X]) ^ j := by
      rw [pow_add, Polynomial.C_mul, ← Polynomial.C_pow]
    rw [hC]
    ring
  have hprod : (∏ j ∈ range n, ((1 : R[X]) + X * C (q ^ (i * n + j)))) =
      ∏ j ∈ range n, (1 + (X * C (q ^ (i * n))) * (C q : R[X]) ^ j) :=
    Finset.prod_congr rfl fun j _ => hfac j
  rw [hprod, prod_one_add_mul_pow_eq_gaussianBinomial]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e1 : ((C q : R[X])) ^ k.choose 2 = C (q ^ k.choose 2) := Polynomial.C_pow.symm
  have e2 : gaussianBinomial (C q : R[X]) n k = C (gaussianBinomial q n k) :=
    (map_gaussianBinomial (C : R →+* R[X]) q n k).symm
  have e3 : ((X : R[X]) * C (q ^ (i * n))) ^ k = C (q ^ (i * n * k)) * X ^ k := by
    rw [mul_pow, ← Polynomial.C_pow, ← pow_mul]
    ring
  rw [e1, e2, e3, pow_add, Polynomial.C_mul, Polynomial.C_mul]
  ring

/-- The block expansion split into its extreme and intermediate halves. -/
private theorem prod_range_block_eq_add {R : Type*} [CommRing R] (q : R) {n : ℕ} (hn : 0 < n)
    (i : ℕ) :
    (∏ j ∈ range n, ((1 : R[X]) + X * C (q ^ (i * n + j)))) =
      babbageBlockMain q n i + babbageBlockError q n i := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hc0 : (0 : ℕ).choose 2 = 0 := rfl
  have h0 : C (q ^ ((0 : ℕ).choose 2 + i * (m + 1) * 0) * gaussianBinomial q (m + 1) 0) *
      (X : R[X]) ^ (0 : ℕ) = 1 := by
    simp only [hc0, mul_zero, add_zero, pow_zero, gaussianBinomial_zero_right, mul_one, one_mul,
      Polynomial.C_1]
  have htop : C (q ^ ((m + 1).choose 2 + i * (m + 1) * (m + 1)) *
        gaussianBinomial q (m + 1) (m + 1)) * (X : R[X]) ^ (m + 1) =
      C (q ^ ((m + 1).choose 2 + i * (m + 1) ^ 2)) * (X : R[X]) ^ (m + 1) := by
    rw [gaussianBinomial_self, mul_one, mul_assoc, ← pow_two]
  unfold babbageBlockMain babbageBlockError
  rw [prod_range_block_eq q (m + 1) i, Finset.sum_range_succ, Finset.sum_range_succ', h0, htop,
    Nat.add_sub_cancel]
  ring

/-! ## The block induction -/

/-- **The block induction.**  Splitting `∏_{j < an} (1 + x qʲ)` into `a` blocks of length
`n` and expanding each of them, the product equals the product of the extreme parts, plus a
remainder `H` that is divisible by `φ` and supported away from multiples of `n`, plus a
remainder `E` divisible by `φ²`.  This is the source text's pairing argument, carried as an
induction invariant. -/
private theorem babbage_block_induction {R : Type*} [CommRing R] (q φ : R) {n : ℕ} (hn : 0 < n)
    (hφ : ∀ k, 0 < k → k < n → φ ∣ gaussianBinomial q n k) (a : ℕ) :
    ∃ H E : R[X],
      (∏ j ∈ range (a * n), ((1 : R[X]) + X * C (q ^ j))) =
          (∏ i ∈ range a, babbageBlockMain q n i) + H + E ∧
        (∀ k, n ∣ k → H.coeff k = 0) ∧ (C φ : R[X]) ∣ H ∧ (C φ : R[X]) ^ 2 ∣ E := by
  induction a with
  | zero =>
      refine ⟨0, 0, ?_, fun k _ => Polynomial.coeff_zero k, dvd_zero _, dvd_zero _⟩
      rw [Nat.zero_mul, Finset.prod_range_zero, Finset.prod_range_zero, add_zero, add_zero]
  | succ a ih =>
      obtain ⟨H, E, heq, hHc, hHd, hEd⟩ := ih
      refine ⟨(∏ i ∈ range a, babbageBlockMain q n i) * babbageBlockError q n a +
          H * babbageBlockMain q n a,
        H * babbageBlockError q n a + E * babbageBlockMain q n a +
          E * babbageBlockError q n a, ?_, ?_, ?_, ?_⟩
      · have hsplit : (∏ j ∈ range ((a + 1) * n), ((1 : R[X]) + X * C (q ^ j))) =
            (∏ j ∈ range (a * n), ((1 : R[X]) + X * C (q ^ j))) *
              ∏ j ∈ range n, ((1 : R[X]) + X * C (q ^ (a * n + j))) := by
          rw [add_one_mul, Finset.prod_range_add]
        rw [hsplit, heq, prod_range_block_eq_add q hn a, Finset.prod_range_succ]
        ring
      · intro k hk
        have h1 : ((∏ i ∈ range a, babbageBlockMain q n i) *
            babbageBlockError q n a).coeff k = 0 :=
          coeff_mul_eq_zero_of_dvd (coeff_prod_babbageBlockMain_eq_zero q n a)
            (coeff_babbageBlockError_eq_zero q n a) k hk
        have h2 : (H * babbageBlockMain q n a).coeff k = 0 := by
          rw [mul_comm]
          exact coeff_mul_eq_zero_of_dvd (coeff_babbageBlockMain_eq_zero q n a) hHc k hk
        rw [Polynomial.coeff_add, h1, h2, add_zero]
      · exact dvd_add (dvd_mul_of_dvd_right (C_dvd_babbageBlockError q φ hφ a) _)
          (dvd_mul_of_dvd_left hHd _)
      · refine dvd_add (dvd_add ?_ (dvd_mul_of_dvd_left hEd _)) (dvd_mul_of_dvd_left hEd _)
        rw [pow_two]
        exact mul_dvd_mul hHd (C_dvd_babbageBlockError q φ hφ a)

/-! ## Reading off the coefficient of `x^{bn}` -/

/-- The coefficients of `∏_{j<N}(1 + x qʲ)`, restated for the shape used here. -/
private theorem coeff_prod_one_add_X_mul_C_pow {R : Type*} [CommRing R] (q : R) (N k : ℕ) :
    (∏ j ∈ range N, ((1 : R[X]) + X * C (q ^ j))).coeff k =
      q ^ k.choose 2 * gaussianBinomial q N k := by
  have hprod : finiteQPochhammerIn (-X : R[X]) (C q) N =
      ∏ j ∈ range N, ((1 : R[X]) + X * C (q ^ j)) := by
    rw [finiteQPochhammerIn]
    exact Finset.prod_congr rfl fun j _ => by rw [Polynomial.C_pow]; ring
  rw [← hprod, coeff_finiteQPochhammerIn_neg_X]

/-- The coefficient of `x^{bn}` in the product of the extreme parts is exactly the
`q^{n²}`-Gaussian coefficient, up to the monomial `q^{C(bn,2)}`. -/
private theorem coeff_prod_babbageBlockMain {R : Type*} [CommRing R] (q : R) {n : ℕ} (hn : 0 < n)
    (a b : ℕ) (hb : b ≤ a) :
    (∏ i ∈ range a, babbageBlockMain q n i).coeff (b * n) =
      q ^ ((b * n).choose 2) * gaussianBinomial (q ^ n ^ 2) a b := by
  -- rewrite the `i`-th extreme part as `1 + y · Q^i`
  have hfac : ∀ i : ℕ, babbageBlockMain q n i =
      1 + (C (q ^ n.choose 2) * X ^ n) * (C (q ^ n ^ 2) : R[X]) ^ i := by
    intro i
    have h : ((C (q ^ n ^ 2) : R[X])) ^ i = C (q ^ (i * n ^ 2)) := by
      rw [← Polynomial.C_pow, ← pow_mul, mul_comm (n ^ 2) i]
    unfold babbageBlockMain
    rw [h, pow_add, Polynomial.C_mul]
    ring
  have hprod : (∏ i ∈ range a, babbageBlockMain q n i) =
      ∏ i ∈ range a, (1 + (C (q ^ n.choose 2) * X ^ n) * (C (q ^ n ^ 2) : R[X]) ^ i) :=
    Finset.prod_congr rfl fun i _ => hfac i
  -- normalise the terms of Gauss's expansion
  have hterm : ∀ r : ℕ,
      ((C (q ^ n ^ 2) : R[X])) ^ r.choose 2 * gaussianBinomial (C (q ^ n ^ 2) : R[X]) a r *
          ((C (q ^ n.choose 2) : R[X]) * X ^ n) ^ r =
        C (q ^ (n ^ 2 * r.choose 2 + n.choose 2 * r) * gaussianBinomial (q ^ n ^ 2) a r) *
          X ^ (n * r) := by
    intro r
    have e1 : ((C (q ^ n ^ 2) : R[X])) ^ r.choose 2 = C (q ^ (n ^ 2 * r.choose 2)) := by
      rw [← Polynomial.C_pow, ← pow_mul]
    have e2 : gaussianBinomial (C (q ^ n ^ 2) : R[X]) a r = C (gaussianBinomial (q ^ n ^ 2) a r) :=
      (map_gaussianBinomial (C : R →+* R[X]) (q ^ n ^ 2) a r).symm
    have e3 : ((C (q ^ n.choose 2) : R[X]) * X ^ n) ^ r =
        C (q ^ (n.choose 2 * r)) * X ^ (n * r) := by
      rw [mul_pow, ← Polynomial.C_pow, ← pow_mul, ← pow_mul]
    rw [e1, e2, e3, pow_add, Polynomial.C_mul, Polynomial.C_mul]
    ring
  have hsum : (∑ r ∈ range (a + 1),
        ((C (q ^ n ^ 2) : R[X])) ^ r.choose 2 * gaussianBinomial (C (q ^ n ^ 2) : R[X]) a r *
          ((C (q ^ n.choose 2) : R[X]) * X ^ n) ^ r) =
      ∑ r ∈ range (a + 1),
        C (q ^ (n ^ 2 * r.choose 2 + n.choose 2 * r) * gaussianBinomial (q ^ n ^ 2) a r) *
          X ^ (n * r) :=
    Finset.sum_congr rfl fun r _ => hterm r
  -- and extract the coefficient
  have hcoeff : ∀ r ∈ range (a + 1),
      (C (q ^ (n ^ 2 * r.choose 2 + n.choose 2 * r) * gaussianBinomial (q ^ n ^ 2) a r) *
          (X : R[X]) ^ (n * r)).coeff (b * n) =
        if b * n = n * r then
          q ^ (n ^ 2 * r.choose 2 + n.choose 2 * r) * gaussianBinomial (q ^ n ^ 2) a r
        else 0 := fun r _ => Polynomial.coeff_C_mul_X_pow _ _ _
  have hsingle : (∑ r ∈ range (a + 1),
      if b * n = n * r then
        q ^ (n ^ 2 * r.choose 2 + n.choose 2 * r) * gaussianBinomial (q ^ n ^ 2) a r
      else 0) =
      (if b * n = n * b then
        q ^ (n ^ 2 * b.choose 2 + n.choose 2 * b) * gaussianBinomial (q ^ n ^ 2) a b
      else 0) := by
    refine Finset.sum_eq_single_of_mem b (Finset.mem_range.mpr (by omega)) fun r _ hrb => ?_
    have hne : ¬ (b * n = n * r) := by
      intro hcon
      have hnb : n * b = n * r := (mul_comm n b).trans hcon
      exact hrb (Nat.eq_of_mul_eq_mul_left hn hnb).symm
    exact if_neg hne
  rw [hprod, prod_one_add_mul_pow_eq_gaussianBinomial, hsum, Polynomial.finsetSum_coeff,
    Finset.sum_congr rfl hcoeff, hsingle, if_pos (mul_comm b n), choose_two_mul,
    show n ^ 2 * b.choose 2 + n.choose 2 * b = b * n.choose 2 + n ^ 2 * b.choose 2 by ring]

/-! ## The generic congruence -/

/-- **The `q`-Babbage congruence, generic form.**  Over an arbitrary commutative ring `R`,
if `φ` divides every interior Gaussian coefficient `[n,k]_q` (`0 < k < n`), then

`φ² ∣ q^{C(bn,2)} · ([an, bn]_q - [a, b]_{q^{n²}})`.

No hypothesis relating `a` and `b` is needed: for `b > a` both Gaussian coefficients
vanish.  The monomial `q^{C(bn,2)}` cannot be dropped at this level of generality, since
`q` need not be invertible; over `ℤ[X]` with `q = X` it is stripped in
`gaussianBinomial_q_babbage_int`. -/
theorem sq_dvd_pow_mul_gaussianBinomial_sub {R : Type*} [CommRing R] (q φ : R) {n : ℕ}
    (hn : 0 < n) (hφ : ∀ k, 0 < k → k < n → φ ∣ gaussianBinomial q n k) (a b : ℕ) :
    φ ^ 2 ∣ q ^ ((b * n).choose 2) *
      (gaussianBinomial q (a * n) (b * n) - gaussianBinomial (q ^ n ^ 2) a b) := by
  rcases Nat.lt_or_ge a b with hab | hb
  · -- above the diagonal both sides vanish
    have hlt : a * n < b * n := by
      have h1 : a * n + n ≤ b * n := by
        have h2 : (a + 1) * n ≤ b * n := Nat.mul_le_mul (show a + 1 ≤ b from hab) le_rfl
        rwa [add_one_mul] at h2
      exact lt_of_lt_of_le (lt_add_of_pos_right (a * n) hn) h1
    rw [gaussianBinomial_eq_zero_of_lt q hlt, gaussianBinomial_eq_zero_of_lt (q ^ n ^ 2) hab,
      sub_self, mul_zero]
    exact dvd_zero _
  · have hba : b ≤ a := hb
    obtain ⟨H, E, heq, hHc, -, hEd⟩ := babbage_block_induction q φ hn hφ a
    have hcoeff : (∏ j ∈ range (a * n), ((1 : R[X]) + X * C (q ^ j))).coeff (b * n) =
        ((∏ i ∈ range a, babbageBlockMain q n i) + H + E).coeff (b * n) := by rw [heq]
    rw [coeff_prod_one_add_X_mul_C_pow, Polynomial.coeff_add, Polynomial.coeff_add,
      coeff_prod_babbageBlockMain q hn a b hba, hHc (b * n) (dvd_mul_left n b)] at hcoeff
    obtain ⟨E', hE'⟩ := hEd
    have hEc : E.coeff (b * n) = φ ^ 2 * E'.coeff (b * n) := by
      rw [hE', ← Polynomial.C_pow, Polynomial.coeff_C_mul]
    refine ⟨E'.coeff (b * n), ?_⟩
    rw [mul_sub, hcoeff, hEc]
    ring

/-! ## The classical Babbage congruence -/

/-- **Babbage's congruence** `C(ap, bp) ≡ C(a, b) (mod p²)` for a prime `p`, obtained from
the generic congruence at `q = 1`, `n = p`, `φ = p`. -/
theorem choose_mul_prime_congr {p : ℕ} (hp : p.Prime) (a b : ℕ) :
    (p : ℤ) ^ 2 ∣ ((a * p).choose (b * p) : ℤ) - (a.choose b : ℤ) := by
  have hφ : ∀ k, 0 < k → k < p → (p : ℤ) ∣ gaussianBinomial (1 : ℤ) p k := by
    intro k hk0 hkp
    rw [gaussianBinomial_one]
    exact Int.natCast_dvd_natCast.mpr (hp.dvd_choose_self hk0.ne' hkp)
  have h := sq_dvd_pow_mul_gaussianBinomial_sub (1 : ℤ) (p : ℤ) hp.pos hφ a b
  simpa only [one_pow, one_mul, gaussianBinomial_one] using h

/-! ## The cyclotomic specialization -/

/-- `Φ_n` divides `[n,k]_X` for `0 < k < n`, over every integral domain: in the cyclotomic
factorization of `[n,k]_X` the exponent of `Φ_n` is `n/n - k/n - (n-k)/n = 1`.  The corpus's
carry criterion `cyclotomic_dvd_gaussianBinomial_iff` gives this only over `ℚ`; the
one-directional statement needs no coprimality of distinct cyclotomics and so holds in
full generality. -/
theorem cyclotomic_dvd_gaussianBinomial_of_lt {R : Type*} [CommRing R] [IsDomain R] {n k : ℕ}
    (hk0 : 0 < k) (hkn : k < n) : cyclotomic n R ∣ gaussianBinomial (X : R[X]) n k := by
  have hn : 0 < n := hk0.trans hkn
  have hexp : n / n - k / n - (n - k) / n = 1 := by
    have h1 : n / n = 1 := Nat.div_self hn
    have h2 : k / n = 0 := Nat.div_eq_of_lt hkn
    have h3 : (n - k) / n = 0 := Nat.div_eq_of_lt (by omega)
    omega
  have hmem : cyclotomic n R ^ (n / n - k / n - (n - k) / n) ∣
      ∏ d ∈ Icc 1 n, cyclotomic d R ^ (n / d - k / d - (n - k) / d) :=
    Finset.dvd_prod_of_mem (fun d => cyclotomic d R ^ (n / d - k / d - (n - k) / d))
      (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩)
  rw [hexp, pow_one] at hmem
  rw [gaussianBinomial_X_eq_prod_cyclotomic hkn.le]
  exact hmem

/-- `X` and `Φ_n` are coprime in `R[X]`.  This is the step the source text performs
silently when it divides the congruence by `q^{C(bn,2)}`: it is legitimate precisely
because `Φ_n(0) = ±1`, so `X` is a unit modulo `Φ_n²`. -/
theorem isCoprime_X_cyclotomic {R : Type*} [CommRing R] (n : ℕ) :
    IsCoprime (X : R[X]) (cyclotomic n R) := by
  rcases eq_or_ne n 0 with rfl | hn0
  · rw [Polynomial.cyclotomic_zero]
    exact isCoprime_one_right
  rcases eq_or_ne n 1 with rfl | hn1
  · rw [Polynomial.cyclotomic_one]
    exact ⟨1, -1, by ring⟩
  have hn : 1 < n := by omega
  have h := Polynomial.X_mul_divX_add (cyclotomic n R)
  rw [Polynomial.cyclotomic_coeff_zero R hn, Polynomial.C_1] at h
  exact ⟨-(divX (cyclotomic n R)), 1, by linear_combination -h⟩

/-- **The `q`-Babbage congruence**, over every integral domain:
`[an, bn]_q ≡ [a, b]_{q^{n²}} (mod Φ_n(q)²)` in `R[q]`.  No hypothesis `a ≥ b` is needed.
This is the generic congruence at `q = X`, `φ = Φ_n`, with the monomial `X^{C(bn,2)}`
stripped by coprimality. -/
theorem gaussianBinomial_q_babbage {R : Type*} [CommRing R] [IsDomain R] (a b : ℕ) {n : ℕ}
    (hn : 0 < n) :
    cyclotomic n R ^ 2 ∣
      gaussianBinomial (X : R[X]) (a * n) (b * n) - gaussianBinomial ((X : R[X]) ^ n ^ 2) a b := by
  have hφ : ∀ k, 0 < k → k < n → cyclotomic n R ∣ gaussianBinomial (X : R[X]) n k :=
    fun k hk0 hkn => cyclotomic_dvd_gaussianBinomial_of_lt hk0 hkn
  have hmain := sq_dvd_pow_mul_gaussianBinomial_sub (X : R[X]) (cyclotomic n R) hn hφ a b
  exact ((isCoprime_X_cyclotomic (R := R) n).symm.pow).dvd_of_dvd_mul_left hmain

/-- The `q`-Babbage congruence in `ℤ[q]`, the form in which the source text states it.
Since `Φ_n` is monic this is equivalent to, and formally stronger than, the congruence
in `ℚ[q]`. -/
theorem gaussianBinomial_q_babbage_int (a b : ℕ) {n : ℕ} (hn : 0 < n) :
    cyclotomic n ℤ ^ 2 ∣
      gaussianBinomial (X : ℤ[X]) (a * n) (b * n) - gaussianBinomial ((X : ℤ[X]) ^ n ^ 2) a b :=
  gaussianBinomial_q_babbage a b hn

/-- **The `q`-Babbage congruence over an arbitrary commutative ring**, obtained from the
integral form by `Polynomial.map`.  The integrality hypothesis is only needed to *prove*
the congruence (through the cyclotomic factorization of `[n,k]_X`); the statement itself
transports to every commutative ring. -/
theorem gaussianBinomial_q_babbage_map {R : Type*} [CommRing R] (a b : ℕ) {n : ℕ} (hn : 0 < n) :
    cyclotomic n R ^ 2 ∣
      gaussianBinomial (X : R[X]) (a * n) (b * n) - gaussianBinomial ((X : R[X]) ^ n ^ 2) a b := by
  have hX : (Polynomial.mapRingHom (Int.castRingHom R)) (X : ℤ[X]) = (X : R[X]) := by
    rw [Polynomial.coe_mapRingHom, Polynomial.map_X]
  have hc : (Polynomial.mapRingHom (Int.castRingHom R)) (cyclotomic n ℤ) = cyclotomic n R := by
    rw [Polynomial.coe_mapRingHom, Polynomial.map_cyclotomic]
  have h := _root_.map_dvd (Polynomial.mapRingHom (Int.castRingHom R))
    (gaussianBinomial_q_babbage_int a b hn)
  simpa only [map_sub, map_pow, map_gaussianBinomial, hX, hc] using h

/-! ## The primitive-root corollary -/

/-- If `p²` divides `f`, then `p` divides `f'`.  A purely algebraic replacement for the
source text's "zero of order at least two", valid over every commutative ring and in
particular in positive characteristic. -/
theorem dvd_derivative_of_sq_dvd {R : Type*} [CommRing R] {p f : R[X]} (h : p ^ 2 ∣ f) :
    p ∣ derivative f := by
  obtain ⟨g, rfl⟩ := h
  refine ⟨derivative p * g + (derivative p * g + p * derivative g), ?_⟩
  rw [pow_two, mul_assoc, Polynomial.derivative_mul, Polynomial.derivative_mul]
  ring

/-- `Φ_n` divides the derivative of the difference of the two sides of the `q`-Babbage
congruence. -/
theorem cyclotomic_dvd_derivative_gaussianBinomial_sub {R : Type*} [CommRing R] [IsDomain R]
    (a b : ℕ) {n : ℕ} (hn : 0 < n) :
    cyclotomic n R ∣ derivative (gaussianBinomial (X : R[X]) (a * n) (b * n) -
      gaussianBinomial ((X : R[X]) ^ n ^ 2) a b) :=
  dvd_derivative_of_sq_dvd (gaussianBinomial_q_babbage a b hn)

/-- **The value clause of the primitive-root corollary**, re-derived from the `q`-Babbage
congruence rather than from `q`-Lucas: at a primitive `n`-th root of unity `ζ` one has
`ζ^{n²} = 1`, so `[an, bn]_ζ = C(a,b)`.  The corpus proves the same statement from
`q`-Lucas as `gaussianBinomial_mul_isPrimitiveRoot`; the source text notes that either
route works. -/
theorem gaussianBinomial_mul_isPrimitiveRoot_of_babbage {R : Type*} [CommRing R] [IsDomain R]
    {ζ : R} {n : ℕ} (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) (a b : ℕ) :
    gaussianBinomial ζ (a * n) (b * n) = (a.choose b : R) := by
  have h1 : Polynomial.eval ζ (gaussianBinomial (X : R[X]) (a * n) (b * n)) =
      gaussianBinomial ζ (a * n) (b * n) := by
    have h := map_gaussianBinomial (Polynomial.evalRingHom ζ) (X : R[X]) (a * n) (b * n)
    rwa [Polynomial.coe_evalRingHom, Polynomial.eval_X] at h
  have hz : (ζ : R) ^ n ^ 2 = 1 := by
    rw [pow_two, pow_mul, hζ.pow_eq_one, one_pow]
  have h2 : Polynomial.eval ζ (gaussianBinomial ((X : R[X]) ^ n ^ 2) a b) = (a.choose b : R) := by
    have h := map_gaussianBinomial (Polynomial.evalRingHom ζ) ((X : R[X]) ^ n ^ 2) a b
    rwa [Polynomial.coe_evalRingHom, Polynomial.eval_pow, Polynomial.eval_X, hz,
      gaussianBinomial_one] at h
  have hroot : Polynomial.eval ζ (cyclotomic n R) = 0 := hζ.isRoot_cyclotomic hn
  have hz2 : (0 : R) ^ 2 = 0 := by rw [pow_two, mul_zero]
  obtain ⟨G, hG⟩ := gaussianBinomial_q_babbage (R := R) a b hn
  have he : Polynomial.eval ζ (gaussianBinomial (X : R[X]) (a * n) (b * n) -
      gaussianBinomial ((X : R[X]) ^ n ^ 2) a b) = 0 := by
    rw [hG, Polynomial.eval_mul, Polynomial.eval_pow, hroot, hz2, zero_mul]
  rw [Polynomial.eval_sub, h1, h2, sub_eq_zero] at he
  exact he

/-- **The derivative clause of the primitive-root corollary**: the two sides of the
`q`-Babbage congruence have the same derivative at `q = ζ`, for every primitive `n`-th
root of unity `ζ` in an integral domain. -/
theorem eval_derivative_gaussianBinomial_mul_isPrimitiveRoot {R : Type*} [CommRing R] [IsDomain R]
    {ζ : R} {n : ℕ} (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) (a b : ℕ) :
    Polynomial.eval ζ (derivative (gaussianBinomial (X : R[X]) (a * n) (b * n))) =
      Polynomial.eval ζ (derivative (gaussianBinomial ((X : R[X]) ^ n ^ 2) a b)) := by
  have hroot : Polynomial.eval ζ (cyclotomic n R) = 0 := hζ.isRoot_cyclotomic hn
  obtain ⟨G, hG⟩ := cyclotomic_dvd_derivative_gaussianBinomial_sub (R := R) a b hn
  have he : Polynomial.eval ζ (derivative (gaussianBinomial (X : R[X]) (a * n) (b * n) -
      gaussianBinomial ((X : R[X]) ^ n ^ 2) a b)) = 0 := by
    rw [hG, Polynomial.eval_mul, hroot, zero_mul]
  rw [Polynomial.derivative_sub, Polynomial.eval_sub, sub_eq_zero] at he
  exact he

end Fabius
