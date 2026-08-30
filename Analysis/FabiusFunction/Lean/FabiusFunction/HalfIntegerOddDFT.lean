import FabiusFunction.ThueMorseFourierInversion
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Odd-frequency DFT traces and the half-integer Ramanujan filter

The half-integer spectral frontier folds the Fourier modes with odd labels
modulo `2 * N`.  Its finite algebraic core is a particularly clean
root-of-unity filter:

`sum_{k < N} zeta ^ ((2 * k + 1) * S)
  = N * (-1) ^ (S / N)` when `N ∣ S`, and is zero otherwise,

provided `zeta` is a primitive `(2 * N)`-th root of unity.  This file proves
that identity over an arbitrary commutative domain and then pushes it through
every power of a finite odd-frequency discrete Fourier transform.  The result
is an all-order odd-coset-filtered convolution formula underlying the
cyclotomic power traces in the half-integer report.  For the report's
power-of-two modulus the odd labels are precisely the units, so this becomes
the classical Ramanujan filter; for arbitrary `N` it is the more general odd
coset rather than the unit group.

Everything here is finite algebra.  There are no infinite sums, no Fourier
series, no termwise differentiation, and no decay or limiting arguments.
In particular, the theorems do **not** assert the analytic alias identity for
the Rvachev product; they supply the exact finite character algebra to which
that later analytic theorem can be attached.

The development is deliberately more general than the dyadic application:
`N` need not be a power of two, and the coefficient ring may be any
commutative domain containing the chosen primitive root.

Main declarations:

* `sum_odd_powers_eq_root_filter` is the raw odd-coset geometric filter.
* `primitive_evenRoot_half_pow_eq_neg_one` identifies the half-period of a
  primitive even-order root with `-1`.
* `sum_odd_powers_eq_ramanujan` is the explicit divisibility-and-sign
  odd-coset filter, specializing to the classical Ramanujan filter at dyadic
  `N`.
* `oddDFT` and `oddDFTPowerTrace` are the unnormalized odd-frequency DFT and
  its full power trace; `oddDFT_add_period` records the period-`N` label
  identity.
* `oddDFTPowerTrace_eq_indexSumExpansion` separates the universal multinomial
  expansion from the later root-of-unity filter.
* `oddRamanujanConvolution` is the congruence-filtered coefficient
  convolution.
* `oddDFTPowerTrace_eq_ramanujanConvolution` is the all-order trace formula.
* `normalizedOddDFTPowerTrace_eq_ramanujanConvolution` gives the normalization
  used by Fourier coefficients.
* `sum_range_two_mul_eq_add_self_sum_of_reflect` isolates the purely additive
  folding step that changes a full odd orbit into a half orbit once the
  required reflection symmetry has been proved; its semiring-valued wrapper
  collects the two halves as multiplication by `2`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ## The odd-coset root-of-unity filter -/

/-- The odd powers form a shifted geometric progression.  If `z ^ (2 * N) = 1`,
then summing the characters with labels `1, 3, ..., 2N - 1` detects whether
`z ^ (2 * S)` is one.

This raw form is useful even without primitivity: the surviving value retains
the phase `z ^ S`. -/
theorem sum_odd_powers_eq_root_filter {R : Type*} [CommRing R] [IsDomain R]
    [DecidableEq R]
    (z : R) (N S : ℕ) (hz : z ^ (2 * N) = 1) :
    ∑ k ∈ range N, z ^ ((2 * k + 1) * S) =
      if z ^ (2 * S) = 1 then (N : R) * z ^ S else 0 := by
  have hperiod : (z ^ (2 * S)) ^ N = 1 := by
    calc
      (z ^ (2 * S)) ^ N = z ^ ((2 * S) * N) :=
        (pow_mul z (2 * S) N).symm
      _ = z ^ ((2 * N) * S) := by congr 1; ring
      _ = (z ^ (2 * N)) ^ S := by rw [pow_mul]
      _ = 1 := by rw [hz, one_pow]
  have hterm : ∀ k ∈ range N,
      z ^ ((2 * k + 1) * S) = z ^ S * (z ^ (2 * S)) ^ k := by
    intro k _
    rw [show (2 * k + 1) * S = S + (2 * S) * k by ring,
      pow_add, pow_mul]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    sum_pow_eq_ite (z ^ (2 * S)) N hperiod]
  split_ifs <;> simp [mul_comm]

/-- Cancelling the common factor two in the divisibility condition which
appears in the odd-coset filter. -/
lemma two_mul_dvd_two_mul_iff (N S : ℕ) :
    2 * N ∣ 2 * S ↔ N ∣ S := by
  exact mul_dvd_mul_iff_left (by norm_num : (2 : ℕ) ≠ 0)

/-- For a primitive root of order `2 * N`, the raw filter condition is exactly
the congruence condition `N ∣ S`.  This version retains the root-valued phase;
`sum_odd_powers_eq_ramanujan` evaluates that phase as an alternating sign. -/
theorem sum_odd_powers_eq_dvd {R : Type*} [CommRing R] [IsDomain R]
    {ζ : R} {N : ℕ} (hζ : IsPrimitiveRoot ζ (2 * N)) (S : ℕ) :
    ∑ k ∈ range N, ζ ^ ((2 * k + 1) * S) =
      if N ∣ S then (N : R) * ζ ^ S else 0 := by
  classical
  rw [sum_odd_powers_eq_root_filter ζ N S hζ.pow_eq_one,
    hζ.pow_eq_one_iff_dvd (2 * S), two_mul_dvd_two_mul_iff]
  by_cases h : N ∣ S <;> simp [h]

/-- The half-period of a primitive root of even order is `-1`.

The proof does not assume characteristic zero.  The power `ζ ^ N` is itself
a primitive square root of unity, and a primitive square root is `-1` in any
commutative domain. -/
theorem primitive_evenRoot_half_pow_eq_neg_one {R : Type*}
    [CommRing R] [IsDomain R] {ζ : R} {N : ℕ}
    (hζ : IsPrimitiveRoot ζ (2 * N)) (hN : 0 < N) :
    ζ ^ N = -1 := by
  have hhalf : IsPrimitiveRoot (ζ ^ N) 2 := by
    exact IsPrimitiveRoot.pow (by omega) hζ (by ring)
  exact IsPrimitiveRoot.eq_neg_one_of_two_right hhalf

/-- **Odd-coset character filter.**  A primitive `(2 * N)`-th root turns the
sum over all odd frequency labels into the signed congruence detector

`N * (-1) ^ (S / N) * [N ∣ S]`.

This is the finite character identity used by every power trace in the
half-integer spectral report.  When `N` is a power of two, the odd labels are
the units modulo `2 * N` and this is the classical Ramanujan sum; for general
`N` the theorem intentionally sums the whole odd coset. -/
theorem sum_odd_powers_eq_ramanujan {R : Type*} [CommRing R] [IsDomain R]
    {ζ : R} {N : ℕ} (hζ : IsPrimitiveRoot ζ (2 * N))
    (hN : 0 < N) (S : ℕ) :
    ∑ k ∈ range N, ζ ^ ((2 * k + 1) * S) =
      if N ∣ S then (N : R) * (-1 : R) ^ (S / N) else 0 := by
  rw [sum_odd_powers_eq_dvd hζ S]
  split_ifs with hS
  · have hphase : ζ ^ S = (-1 : R) ^ (S / N) := by
      conv_lhs => rw [← Nat.mul_div_cancel' hS]
      rw [pow_mul, primitive_evenRoot_half_pow_eq_neg_one hζ hN]
    rw [hphase]
  · rfl

/-! ## Odd-frequency DFT power traces -/

/-- The unnormalized discrete Fourier coefficient at the odd label `2k+1`,
for a block of length `2 * N`.  Its definition only needs a semiring;
additive inverses and commutative multiplication enter later, when the
half-period phase and all-order product expansion are used. -/
def oddDFT {R : Type*} [Semiring R] (ζ : R) (N : ℕ)
    (f : Fin (2 * N) → R) (k : ℕ) : R :=
  ∑ j : Fin (2 * N), f j * ζ ^ ((2 * k + 1) * j.val)

/-- Odd-frequency labels are periodic modulo `N` as soon as `ζ` has period
`2 * N`.  Primitivity and the domain hypotheses used by the Ramanujan filter
are not needed for this elementary fact. -/
theorem oddDFT_add_period {R : Type*} [Semiring R]
    {ζ : R} {N : ℕ} (hζ : ζ ^ (2 * N) = 1)
    (f : Fin (2 * N) → R) (k : ℕ) :
    oddDFT ζ N f (k + N) = oddDFT ζ N f k := by
  classical
  unfold oddDFT
  refine Finset.sum_congr rfl (fun j _hj => ?_)
  have hperiod : ζ ^ ((2 * N) * j.val) = 1 := by
    rw [pow_mul, hζ, one_pow]
  rw [show (2 * (k + N) + 1) * j.val =
      (2 * k + 1) * j.val + (2 * N) * j.val by ring,
    pow_add, hperiod, mul_one]

/-- The full power trace over the `N` odd frequency labels modulo `2 * N`. -/
def oddDFTPowerTrace {R : Type*} [Semiring R] (ζ : R) (N : ℕ)
    (f : Fin (2 * N) → R) (m : ℕ) : R :=
  ∑ k ∈ range N, oddDFT ζ N f k ^ m

/-- The sum of the sample indices in an `m`-tuple.  The Ramanujan filter only
depends on a tuple through this single additive statistic. -/
def oddDFTIndexSum {N m : ℕ} (J : Fin m → Fin (2 * N)) : ℕ :=
  ∑ ℓ : Fin m, (J ℓ).val

/-- **Universal odd-DFT trace expansion.**  Before using any
root-of-unity orthogonality, an `m`-th power trace is a sum over sample
tuples, and its character depends on a tuple only through
`oddDFTIndexSum`.  This purely distributive layer works over every
commutative semiring. -/
theorem oddDFTPowerTrace_eq_indexSumExpansion {R : Type*}
    [CommSemiring R] (ζ : R) (N : ℕ)
    (f : Fin (2 * N) → R) (m : ℕ) :
    oddDFTPowerTrace ζ N f m =
      ∑ J : Fin m → Fin (2 * N),
        (∏ ℓ : Fin m, f (J ℓ)) *
          ∑ k ∈ range N,
            ζ ^ ((2 * k + 1) * oddDFTIndexSum J) := by
  classical
  unfold oddDFTPowerTrace oddDFT
  calc
    ∑ k ∈ range N,
        (∑ j : Fin (2 * N), f j * ζ ^ ((2 * k + 1) * j.val)) ^ m =
        ∑ k ∈ range N, ∑ J : Fin m → Fin (2 * N),
          ∏ ℓ : Fin m,
            (f (J ℓ) * ζ ^ ((2 * k + 1) * (J ℓ).val)) := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simpa using
        (Fintype.sum_pow
          (f := fun j : Fin (2 * N) =>
            f j * ζ ^ ((2 * k + 1) * j.val)) m)
    _ = ∑ J : Fin m → Fin (2 * N), ∑ k ∈ range N,
          ∏ ℓ : Fin m,
            (f (J ℓ) * ζ ^ ((2 * k + 1) * (J ℓ).val)) := by
      rw [Finset.sum_comm]
    _ = ∑ J : Fin m → Fin (2 * N),
          (∏ ℓ : Fin m, f (J ℓ)) *
            ∑ k ∈ range N,
              ζ ^ ((2 * k + 1) * oddDFTIndexSum J) := by
      refine Finset.sum_congr rfl (fun J _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      calc
        ∏ ℓ : Fin m,
            (f (J ℓ) * ζ ^ ((2 * k + 1) * (J ℓ).val)) =
            (∏ ℓ : Fin m, f (J ℓ)) *
              ∏ ℓ : Fin m,
                ζ ^ ((2 * k + 1) * (J ℓ).val) := by
          rw [Finset.prod_mul_distrib]
        _ = (∏ ℓ : Fin m, f (J ℓ)) *
              ζ ^ (∑ ℓ : Fin m, (2 * k + 1) * (J ℓ).val) := by
          rw [Finset.prod_pow_eq_pow_sum]
        _ = (∏ ℓ : Fin m, f (J ℓ)) *
              ζ ^ ((2 * k + 1) * oddDFTIndexSum J) := by
          simp only [oddDFTIndexSum, Finset.mul_sum]

/-- The signed, congruence-filtered `m`-fold convolution of a length-`2N`
sample block.  It is defined over any commutative ring and makes no reference
to a root of unity. -/
def oddRamanujanConvolution {R : Type*} [CommRing R] (N m : ℕ)
    (f : Fin (2 * N) → R) : R :=
  ∑ J : Fin m → Fin (2 * N),
    if N ∣ oddDFTIndexSum J then
      (-1 : R) ^ (oddDFTIndexSum J / N) * ∏ ℓ : Fin m, f (J ℓ)
    else 0

/-- **All-order odd-frequency power trace formula.**  The `m`-th powers of
the odd DFT coefficients sum to `N` times a signed congruence-filtered
`m`-fold convolution of the original samples.

This is the finite algebraic content of the odd-coset trace formula,
specializing to the Ramanujan trace formula when `N` is a power of two.  It
holds for every order, including `m = 0`, over every commutative domain
containing a primitive `(2 * N)`-th root. -/
theorem oddDFTPowerTrace_eq_ramanujanConvolution {R : Type*}
    [CommRing R] [IsDomain R] {ζ : R} {N : ℕ}
    (hζ : IsPrimitiveRoot ζ (2 * N)) (hN : 0 < N)
    (f : Fin (2 * N) → R) (m : ℕ) :
    oddDFTPowerTrace ζ N f m =
      (N : R) * oddRamanujanConvolution N m f := by
  classical
  rw [oddDFTPowerTrace_eq_indexSumExpansion]
  unfold oddRamanujanConvolution
  calc
    ∑ J : Fin m → Fin (2 * N),
          (∏ ℓ : Fin m, f (J ℓ)) *
            ∑ k ∈ range N,
              ζ ^ ((2 * k + 1) * oddDFTIndexSum J) =
        ∑ J : Fin m → Fin (2 * N),
          (∏ ℓ : Fin m, f (J ℓ)) *
            (if N ∣ oddDFTIndexSum J then
              (N : R) * (-1 : R) ^ (oddDFTIndexSum J / N)
            else 0) := by
      refine Finset.sum_congr rfl (fun J _ => ?_)
      rw [sum_odd_powers_eq_ramanujan hζ hN]
    _ = ∑ J : Fin m → Fin (2 * N),
          (N : R) *
            (if N ∣ oddDFTIndexSum J then
              (-1 : R) ^ (oddDFTIndexSum J / N) *
                ∏ ℓ : Fin m, f (J ℓ)
            else 0) := by
      refine Finset.sum_congr rfl (fun J _ => ?_)
      split_ifs <;> ring
    _ = (N : R) * ∑ J : Fin m → Fin (2 * N),
          if N ∣ oddDFTIndexSum J then
            (-1 : R) ^ (oddDFTIndexSum J / N) *
              ∏ ℓ : Fin m, f (J ℓ)
          else 0 := by
      rw [Finset.mul_sum]

/-! ## Fourier normalization and half-orbit folding -/

/-- The normalization used for a Fourier coefficient: divide the unnormalized
odd DFT by the half-length `N`. -/
def normalizedOddDFT {F : Type*} [Field F] (ζ : F) (N : ℕ)
    (f : Fin (2 * N) → F) (k : ℕ) : F :=
  (N : F)⁻¹ * oddDFT ζ N f k

/-- The normalized coefficients inherit the same period-`N` identity in
their frequency label. -/
theorem normalizedOddDFT_add_period {F : Type*} [Field F]
    {ζ : F} {N : ℕ} (hζ : ζ ^ (2 * N) = 1)
    (f : Fin (2 * N) → F) (k : ℕ) :
    normalizedOddDFT ζ N f (k + N) = normalizedOddDFT ζ N f k := by
  unfold normalizedOddDFT
  rw [oddDFT_add_period hζ]

/-- The full power trace of the normalized odd-frequency coefficients. -/
def normalizedOddDFTPowerTrace {F : Type*} [Field F] (ζ : F) (N : ℕ)
    (f : Fin (2 * N) → F) (m : ℕ) : F :=
  ∑ k ∈ range N, normalizedOddDFT ζ N f k ^ m

/-- The normalized all-order trace formula.  Its scalar is
`N / N^m = N^(1-m)` in the conventional informal notation. -/
theorem normalizedOddDFTPowerTrace_eq_ramanujanConvolution {F : Type*}
    [Field F] {ζ : F} {N : ℕ}
    (hζ : IsPrimitiveRoot ζ (2 * N)) (hN : 0 < N)
    (f : Fin (2 * N) → F) (m : ℕ) :
    normalizedOddDFTPowerTrace ζ N f m =
      (N : F) / (N : F) ^ m * oddRamanujanConvolution N m f := by
  classical
  unfold normalizedOddDFTPowerTrace normalizedOddDFT
  calc
    ∑ k ∈ range N, ((N : F)⁻¹ * oddDFT ζ N f k) ^ m =
        ∑ k ∈ range N,
          (((N : F)⁻¹) ^ m * oddDFT ζ N f k ^ m) := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [mul_pow]
    _ = ((N : F)⁻¹) ^ m * oddDFTPowerTrace ζ N f m := by
      unfold oddDFTPowerTrace
      rw [Finset.mul_sum]
    _ = ((N : F)⁻¹) ^ m *
          ((N : F) * oddRamanujanConvolution N m f) := by
      rw [oddDFTPowerTrace_eq_ramanujanConvolution hζ hN]
    _ = (N : F) / (N : F) ^ m * oddRamanujanConvolution N m f := by
      rw [div_eq_mul_inv, inv_pow]
      ring

/-- A finite reflection lemma for passing from a full odd orbit to one
representative from each pair.  The hypothesis is intentionally explicit:
the Fourier-algebra layer only uses the reflection once an application has
proved it from the symmetry of its samples or of its analytic Fourier data. -/
theorem sum_range_two_mul_eq_add_self_sum_of_reflect
    {A : Type*} [AddCommMonoid A] (M : ℕ) (g : ℕ → A)
    (hreflect : ∀ k < M, g (2 * M - 1 - k) = g k) :
    ∑ k ∈ range (2 * M), g k =
      (∑ k ∈ range M, g k) + ∑ k ∈ range M, g k := by
  rw [show 2 * M = M + M by ring, Finset.sum_range_add]
  have hupper : ∑ k ∈ range M, g (M + k) = ∑ k ∈ range M, g k := by
    calc
      ∑ k ∈ range M, g (M + k) =
          ∑ k ∈ range M, g (M + (M - 1 - k)) := by
        symm
        exact Finset.sum_range_reflect (fun k => g (M + k)) M
      _ = ∑ k ∈ range M, g k := by
        refine Finset.sum_congr rfl (fun k hk => ?_)
        rw [show M + (M - 1 - k) = 2 * M - 1 - k by
          have hk' := Finset.mem_range.mp hk
          omega]
        exact hreflect k (Finset.mem_range.mp hk)
  rw [hupper]

/-- Semiring-valued form of `sum_range_two_mul_eq_add_self_sum_of_reflect`,
with the two identical halves collected as left multiplication by `2`. -/
theorem sum_range_two_mul_eq_two_mul_sum_of_reflect {R : Type*} [Semiring R]
    (M : ℕ) (g : ℕ → R)
    (hreflect : ∀ k < M, g (2 * M - 1 - k) = g k) :
    ∑ k ∈ range (2 * M), g k = (2 : R) * ∑ k ∈ range M, g k := by
  simpa [two_mul] using
    sum_range_two_mul_eq_add_self_sum_of_reflect M g hreflect

/-- Full-to-half folding for normalized odd DFT power traces.  No sample
symmetry is smuggled into the statement: the caller supplies the exact
reflection identity for the coefficients. -/
theorem normalizedOddDFTPowerTrace_eq_two_mul_half {F : Type*} [Field F]
    (ζ : F) (M : ℕ) (f : Fin (2 * (2 * M)) → F) (m : ℕ)
    (hreflect : ∀ k < M,
      normalizedOddDFT ζ (2 * M) f (2 * M - 1 - k) =
        normalizedOddDFT ζ (2 * M) f k) :
    normalizedOddDFTPowerTrace ζ (2 * M) f m =
      (2 : F) * ∑ k ∈ range M, normalizedOddDFT ζ (2 * M) f k ^ m := by
  unfold normalizedOddDFTPowerTrace
  apply sum_range_two_mul_eq_two_mul_sum_of_reflect
  intro k hk
  rw [hreflect k hk]

end Fabius
