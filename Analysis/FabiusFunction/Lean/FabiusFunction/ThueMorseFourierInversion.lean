import FabiusFunction.ThueMorseFourier
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Finite Fourier inversion for the Thue–Morse block

The dyadic discrete Fourier transform inverts exactly, because the
characters of `ℤ/2^m` are orthogonal — a finite geometric-series fact
requiring no integration.  This module proves the inversion in full
generality (any field, any primitive root of unity, any function) and
specializes it to the Thue–Morse signs, first for an arbitrary
primitive `2^m`-th root of unity in an arbitrary field and then over
`ℂ` with the canonical root `e^(2πi/2^m)`.

* `sum_pow_eq_ite` — root-of-unity orthogonality: for `z^N = 1`,
  `∑_{k<N} z^k` is `N` at `z = 1` and `0` otherwise.  Stated over any
  commutative domain: the telescoped identity `(∑ z^k)·(z-1) = z^N - 1`
  needs no division.
* `sum_pow_mul_inv_pow_eq_ite` — **character orthogonality**
  `∑_{ℓ<q} (ζ^a·ζ^(-b))^ℓ = q·[a ≡ b (mod q)]`, the single fact behind
  both the inversion formula and the root-of-unity filter.
* `sum_filter_modEq_mul_natCast` — **the root-of-unity filter**, over
  any field and any coefficient function `f`:
  `q·∑_{n<N, n≡r (q)} f(n) = ∑_{ℓ<q} (ζ⁻¹)^(rℓ)·∑_{n<N} f(n)ζ^(nℓ)`.
  Character orthogonality plus one sum interchange.
* `dft_inversion_mod` — **finite Fourier inversion with no side
  condition** on the index: with `ζ` a primitive `N`-th root of unity,
  `∑_{k<N} (∑_{n'<N} f(n')·ζ^(k·n'))·(ζ⁻¹)^(k·n) = N·f(n % N)` for every
  `n : ℕ`.  This is the filter with `q = N`: on the block `n' < N` the
  residue class of `n` is the single index `n % N`.  The inverse
  transform is `N`-periodic in `n`, so the block restriction `n < N`
  is only a normalization of the index.
* `dft_inversion` — the same statement on the block `n < N`, where the
  residue `n % N` is `n`.
* `sum_thueMorseSign_pow_mul` — the **twisted block transform as a finite
  product**: over any commutative ring,
  `∑_{n<2^m} ε(n)·z^(n·ℓ) = ∏_{j<m} (1 - z^(ℓ·2^j))`.
* `thueMorse_dft_inversion'` — the root-of-unity formula for the
  individual sign over any field, for any primitive `2^m`-th root of
  unity `ζ`: `∑_{k<2^m} ε̂(k)·ζ^(k·n) = 2^m·ε(n)`, where
  `ε̂(k) = ∑_{n'} ε(n')·ζ^(-k·n')` is the dyadic DFT.
* `thueMorse_dft_inversion_prod'` — the same with the transform written
  in closed product form,
  `∑_{k<2^m} (∏_{j<m}(1 - ζ^(k·2^j)))·(ζ⁻¹)^(k·n) = 2^m·ε(n)`.
* `isPrimitiveRoot_exp_two_pow` — `e^(2πi/2^m)` is a primitive
  `2^m`-th root of unity in `ℂ`.
* `thueMorse_dft_inversion`, `thueMorse_dft_inversion_prod` — the
  atlas's formulas over `ℂ` with `ζ = e^(2πi/2^m)`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- **Root-of-unity orthogonality**: if `z^N = 1` then `∑_{k<N} z^k` is
`N` for `z = 1` and `0` otherwise.

A commutative domain suffices — no field structure is used.  Away from
`z = 1` the telescoped identity `(∑_{k<N} z^k)·(z - 1) = z^N - 1 = 0`
exhibits the sum as a zero divisor against the nonzero element `z - 1`,
which already forces it to vanish; the division `(z^N - 1)/(z - 1)` of
the field proof is never needed. -/
theorem sum_pow_eq_ite {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]
    (z : R) (N : ℕ) (hz : z ^ N = 1) :
    ∑ k ∈ range N, z ^ k = if z = 1 then (N : R) else 0 := by
  by_cases h1 : z = 1
  · subst h1
    simp
  · rw [if_neg h1]
    have h0 : (∑ k ∈ range N, z ^ k) * (z - 1) = 0 := by
      rw [geom_sum_mul, hz, sub_self]
    rcases mul_eq_zero.mp h0 with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) h1

/-- **Character orthogonality over a full period**, in the shape both finite
transforms of the atlas need: for a primitive `q`-th root of unity `ζ` in any
field, the geometric sum of `ζ^a·(ζ⁻¹)^b` over `ℓ < q` detects the congruence
`a ≡ b (mod q)`.  Both the inversion formula and the root-of-unity filter are
this lemma plus a sum interchange. -/
theorem sum_pow_mul_inv_pow_eq_ite {F : Type*} [Field F] [DecidableEq F]
    {ζ : F} {q : ℕ} (hζ : IsPrimitiveRoot ζ q) (hq : q ≠ 0) (a b : ℕ) :
    ∑ ℓ ∈ range q, (ζ ^ a * (ζ⁻¹) ^ b) ^ ℓ =
      if a % q = b % q then (q : F) else 0 := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hq
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq
  have hw : (ζ ^ a * (ζ⁻¹) ^ b) ^ q = 1 := by
    have h1 : ζ ^ (a * q) = 1 := by
      rw [mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have h2 : (ζ⁻¹) ^ (b * q) = 1 := by
      rw [mul_comm, pow_mul, inv_pow, hζ.pow_eq_one, inv_one, one_pow]
    rw [mul_pow, ← pow_mul, ← pow_mul, h1, h2, one_mul]
  rw [sum_pow_eq_ite _ q hw]
  have hpowmod : ∀ c : ℕ, ζ ^ c = ζ ^ (c % q) := by
    intro c
    conv_lhs => rw [← Nat.div_add_mod c q]
    rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  have hiff : (ζ ^ a * (ζ⁻¹) ^ b = 1) ↔ (a % q = b % q) := by
    rw [inv_pow, mul_inv_eq_one₀ (pow_ne_zero b hζ0)]
    constructor
    · intro h
      rw [hpowmod a, hpowmod b] at h
      exact hζ.pow_inj (Nat.mod_lt _ hqpos) (Nat.mod_lt _ hqpos) h
    · intro h
      rw [hpowmod a, hpowmod b, h]
  simp only [hiff]

/-- **The root-of-unity filter**, in full generality: for a primitive
`q`-th root of unity `ζ` in a field and any `f`, the progression
`n ≡ r (mod q)` is extracted from `range N` by averaging twisted
transforms:
`q·∑_{n<N, n≡r} f(n) = ∑_{ℓ<q} (ζ⁻¹)^(rℓ)·∑_{n<N} f(n)ζ^(nℓ)`. -/
theorem sum_filter_modEq_mul_natCast {F : Type*} [Field F] [DecidableEq F]
    {ζ : F} {q : ℕ} (hζ : IsPrimitiveRoot ζ q) (hq : q ≠ 0)
    (f : ℕ → F) (N r : ℕ) :
    (q : F) * ∑ n ∈ (range N).filter (fun n => n % q = r % q), f n =
      ∑ ℓ ∈ range q, (ζ⁻¹) ^ (r * ℓ) * ∑ n ∈ range N, f n * ζ ^ (n * ℓ) := by
  symm
  have hstep : ∀ ℓ ∈ range q,
      (ζ⁻¹) ^ (r * ℓ) * ∑ n ∈ range N, f n * ζ ^ (n * ℓ) =
      ∑ n ∈ range N, f n * (ζ ^ n * (ζ⁻¹) ^ r) ^ ℓ := by
    intro ℓ _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    have hsplit : (ζ ^ n * (ζ⁻¹) ^ r) ^ ℓ =
        ζ ^ (n * ℓ) * (ζ⁻¹) ^ (r * ℓ) := by
      rw [mul_pow, ← pow_mul, ← pow_mul]
    rw [hsplit]
    ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  have hinner : ∀ n ∈ range N,
      ∑ ℓ ∈ range q, f n * (ζ ^ n * (ζ⁻¹) ^ r) ^ ℓ =
      f n * (if n % q = r % q then (q : F) else 0) := by
    intro n _
    rw [← Finset.mul_sum, sum_pow_mul_inv_pow_eq_ite hζ hq n r]
  rw [Finset.sum_congr rfl hinner, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs <;> ring

/-- **Finite Fourier inversion, with no restriction on the index.**  For a
primitive `N`-th root of unity `ζ` and any `f`, the inverse transform of
the transform returns `N·f(n % N)`.

This is the root-of-unity filter `sum_filter_modEq_mul_natCast` with
modulus `q = N` and residue `r = n`: on the block `n' < N` the class
`n' ≡ n (mod N)` consists of the single index `n % N`.  The inverse
transform depends on `n` only through `ζ^n`, hence only through
`n % N`; the value it recovers is therefore the coefficient at the
residue of `n`.  On the block `n < N` this is `f n` — see
`dft_inversion`. -/
theorem dft_inversion_mod {F : Type*} [Field F] [DecidableEq F] {ζ : F}
    {N : ℕ} (hζ : IsPrimitiveRoot ζ N) (hN : N ≠ 0) (f : ℕ → F) (n : ℕ) :
    ∑ k ∈ range N,
        (∑ n' ∈ range N, f n' * ζ ^ (k * n')) * (ζ⁻¹) ^ (k * n) =
      (N : F) * f (n % N) := by
  -- on the block the residue class of `n` is the single index `n % N`
  have hfilter :
      ∑ n' ∈ (range N).filter (fun n' => n' % N = n % N), f n' =
        f (n % N) := by
    rw [Finset.sum_filter]
    have hcollapse : ∀ n' ∈ range N,
        (if n' % N = n % N then f n' else 0) =
          (if n' = n % N then f n' else 0) := by
      intro n' hn'
      rw [Nat.mod_eq_of_lt (Finset.mem_range.mp hn')]
    rw [Finset.sum_congr rfl hcollapse,
      Finset.sum_ite_eq' (range N) (n % N) f,
      if_pos (Finset.mem_range.mpr
        (Nat.mod_lt n (Nat.pos_of_ne_zero hN)))]
  rw [← hfilter, sum_filter_modEq_mul_natCast hζ hN f N n]
  -- the two sides differ only by commuting the exponents and factors
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm n k, mul_comm ((ζ⁻¹) ^ (k * n))]
  congr 1
  exact Finset.sum_congr rfl fun n' _ => by rw [mul_comm k n']

/-- **Finite Fourier inversion** over an arbitrary field: for a primitive
`N`-th root of unity `ζ` and any `f`, the inverse transform of the
transform returns `N·f(n)` on the block. -/
theorem dft_inversion {F : Type*} [Field F] [DecidableEq F] {ζ : F} {N : ℕ}
    (hζ : IsPrimitiveRoot ζ N) (hN : N ≠ 0)
    (f : ℕ → F) (n : ℕ) (hn : n < N) :
    ∑ k ∈ range N,
        (∑ n' ∈ range N, f n' * ζ ^ (k * n')) * (ζ⁻¹) ^ (k * n) =
      (N : F) * f n := by
  rw [dft_inversion_mod hζ hN f n, Nat.mod_eq_of_lt hn]

/-- **The twisted Thue–Morse block transform is a finite product.**  Over
any commutative ring, for every step `ℓ`,
`∑_{n<2^m} ε(n)·z^(n·ℓ) = ∏_{j<m} (1 - z^(ℓ·2^j))`.

This is the master product `prod_one_sub_pow_eq_sum_thueMorseSign`
evaluated at `z^ℓ`, with the exponents flattened; it is the shape in
which every character sum of the atlas meets the block polynomial. -/
theorem sum_thueMorseSign_pow_mul {R : Type*} [CommRing R] (z : R)
    (m ℓ : ℕ) :
    ∑ n ∈ range (2 ^ m), ((thueMorseSign n : ℤ) : R) * z ^ (n * ℓ) =
      ∏ j ∈ range m, (1 - z ^ (ℓ * 2 ^ j)) := by
  calc ∑ n ∈ range (2 ^ m), ((thueMorseSign n : ℤ) : R) * z ^ (n * ℓ)
      = ∑ n ∈ range (2 ^ m), ((thueMorseSign n : ℤ) : R) * (z ^ ℓ) ^ n :=
        Finset.sum_congr rfl fun n _ => by rw [← pow_mul, mul_comm ℓ n]
    _ = ∏ j ∈ range m, (1 - (z ^ ℓ) ^ (2 ^ j)) :=
        (prod_one_sub_pow_eq_sum_thueMorseSign (z ^ ℓ) m).symm
    _ = ∏ j ∈ range m, (1 - z ^ (ℓ * 2 ^ j)) :=
        Finset.prod_congr rfl fun j _ => by rw [← pow_mul]

/-- **The root-of-unity formula for the individual sign, over any
field**: for a primitive `2^m`-th root of unity `ζ`, the inverse
transform of the dyadic DFT `ε̂(k) = ∑_{n'} ε(n')·ζ^(-k·n')` recovers
`2^m·ε(n)` on the block.  This is `dft_inversion` for `f = ε`. -/
theorem thueMorse_dft_inversion' {F : Type*} [Field F] [DecidableEq F]
    {ζ : F} {m n : ℕ} (hζ : IsPrimitiveRoot ζ (2 ^ m))
    (hn : n < 2 ^ m) :
    ∑ k ∈ range (2 ^ m),
        (∑ n' ∈ range (2 ^ m), ((thueMorseSign n' : ℤ) : F) *
            ζ ^ (k * n')) * (ζ⁻¹) ^ (k * n) =
      ((2 ^ m : ℕ) : F) * ((thueMorseSign n : ℤ) : F) :=
  dft_inversion hζ (Nat.two_pow_pos m).ne'
    (fun n' => ((thueMorseSign n' : ℤ) : F)) n hn

/-- **The root-of-unity formula in closed product form, over any
field.**  Substituting `sum_thueMorseSign_pow_mul` for the dyadic DFT
turns `thueMorse_dft_inversion'` into a statement with no inner sum:
`∑_{k<2^m} (∏_{j<m} (1 - ζ^(k·2^j)))·(ζ⁻¹)^(k·n) = 2^m·ε(n)` for any
primitive `2^m`-th root of unity `ζ` and `n < 2^m`. -/
theorem thueMorse_dft_inversion_prod' {F : Type*} [Field F]
    [DecidableEq F] {ζ : F} {m n : ℕ} (hζ : IsPrimitiveRoot ζ (2 ^ m))
    (hn : n < 2 ^ m) :
    ∑ k ∈ range (2 ^ m),
        (∏ j ∈ range m, (1 - ζ ^ (k * 2 ^ j))) * (ζ⁻¹) ^ (k * n) =
      ((2 ^ m : ℕ) : F) * ((thueMorseSign n : ℤ) : F) := by
  have hprod : ∀ k : ℕ,
      ∏ j ∈ range m, (1 - ζ ^ (k * 2 ^ j)) =
        ∑ n' ∈ range (2 ^ m), ((thueMorseSign n' : ℤ) : F) *
          ζ ^ (k * n') := by
    intro k
    rw [← sum_thueMorseSign_pow_mul ζ m k]
    exact Finset.sum_congr rfl fun n' _ => by rw [mul_comm k n']
  rw [← thueMorse_dft_inversion' hζ hn]
  exact Finset.sum_congr rfl fun k _ => by rw [hprod k]

/-- `e^(2πi/2^m)` is a primitive `2^m`-th root of unity in `ℂ`. -/
theorem isPrimitiveRoot_exp_two_pow (m : ℕ) :
    IsPrimitiveRoot
      (Complex.exp (2 * Real.pi * Complex.I / (2 ^ m))) (2 ^ m) := by
  have h := Complex.isPrimitiveRoot_exp (2 ^ m) (Nat.two_pow_pos m).ne'
  convert h using 2
  push_cast
  ring

/-- **The atlas's root-of-unity formula for the individual sign**: over
`ℂ` with `ζ = e^(2πi/2^m)`, the inverse transform of the dyadic DFT
`ε̂(k) = ∑_{n'} ε(n')·ζ^(-k·n')` recovers `2^m·ε(n)` on the block. -/
theorem thueMorse_dft_inversion (m n : ℕ) (hn : n < 2 ^ m) :
    ∑ k ∈ range (2 ^ m),
        (∑ n' ∈ range (2 ^ m), ((thueMorseSign n' : ℤ) : ℂ) *
            Complex.exp (2 * Real.pi * Complex.I / (2 ^ m)) ^ (k * n')) *
          ((Complex.exp (2 * Real.pi * Complex.I / (2 ^ m)))⁻¹) ^ (k * n) =
      ((2 ^ m : ℕ) : ℂ) * ((thueMorseSign n : ℤ) : ℂ) :=
  thueMorse_dft_inversion' (isPrimitiveRoot_exp_two_pow m) hn

/-- **The root-of-unity formula in closed product form.**  Substituting
`sum_thueMorseSign_pow_mul` for the dyadic DFT turns
`thueMorse_dft_inversion` into a statement with no inner sum:
`∑_{k<2^m} (∏_{j<m} (1 - ζ^(k·2^j)))·(ζ⁻¹)^(k·n) = 2^m·ε(n)` for
`ζ = e^(2πi/2^m)` and `n < 2^m`. -/
theorem thueMorse_dft_inversion_prod (m n : ℕ) (hn : n < 2 ^ m) :
    ∑ k ∈ range (2 ^ m),
        (∏ j ∈ range m, (1 - Complex.exp
            (2 * Real.pi * Complex.I / (2 ^ m)) ^ (k * 2 ^ j))) *
          ((Complex.exp (2 * Real.pi * Complex.I / (2 ^ m)))⁻¹) ^ (k * n) =
      ((2 ^ m : ℕ) : ℂ) * ((thueMorseSign n : ℤ) : ℂ) :=
  thueMorse_dft_inversion_prod' (isPrimitiveRoot_exp_two_pow m) hn

end Fabius
