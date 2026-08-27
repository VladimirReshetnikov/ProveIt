import FabiusFunction.ThueMorseFourier
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Finite Fourier inversion for the Thue–Morse block

The dyadic discrete Fourier transform inverts exactly, because the
characters of `ℤ/2^m` are orthogonal — a finite geometric-series fact
requiring no integration.  This module proves the inversion in full
generality (any field, any primitive root of unity, any function) and
specializes it to the Thue–Morse signs over `ℂ`.

* `sum_pow_eq_ite` — root-of-unity orthogonality: for `z^N = 1`,
  `∑_{k<N} z^k` is `N` at `z = 1` and `0` otherwise.
* `sum_pow_mul_inv_pow_eq_ite` — **character orthogonality**
  `∑_{ℓ<q} (ζ^a·ζ^(-b))^ℓ = q·[a ≡ b (mod q)]`, the single fact behind
  both the inversion formula and the root-of-unity filter.
* `dft_inversion` — **finite Fourier inversion** over any field: with
  `ζ` a primitive `N`-th root of unity,
  `∑_{k<N} (∑_{n'<N} f(n')·ζ^(k·n'))·(ζ⁻¹)^(k·n) = N·f(n)` for `n < N`.
* `thueMorse_dft_inversion` — the atlas's root-of-unity formula for the
  individual sign: over `ℂ` with `ζ = e^(2πi/2^m)`,
  `∑_{k<2^m} ε̂(k)·ζ^(k·n) = 2^m·ε(n)`, where
  `ε̂(k) = ∑_{n'} ε(n')·ζ^(-k·n')` is the dyadic DFT.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- **Root-of-unity orthogonality**: if `z^N = 1` then `∑_{k<N} z^k` is
`N` for `z = 1` and `0` otherwise. -/
theorem sum_pow_eq_ite {F : Type*} [Field F] [DecidableEq F] (z : F) (N : ℕ)
    (hz : z ^ N = 1) :
    ∑ k ∈ range N, z ^ k = if z = 1 then (N : F) else 0 := by
  by_cases h1 : z = 1
  · subst h1
    simp
  · rw [if_neg h1, geom_sum_eq h1, hz, sub_self, zero_div]

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

/-- **Finite Fourier inversion** over an arbitrary field: for a primitive
`N`-th root of unity `ζ` and any `f`, the inverse transform of the
transform returns `N·f(n)` on the block. -/
theorem dft_inversion {F : Type*} [Field F] [DecidableEq F] {ζ : F} {N : ℕ}
    (hζ : IsPrimitiveRoot ζ N) (hN : N ≠ 0)
    (f : ℕ → F) (n : ℕ) (hn : n < N) :
    ∑ k ∈ range N,
        (∑ n' ∈ range N, f n' * ζ ^ (k * n')) * (ζ⁻¹) ^ (k * n) =
      (N : F) * f n := by
  -- push the outer factor inside and swap the sums
  have hexpand : ∀ k ∈ range N,
      (∑ n' ∈ range N, f n' * ζ ^ (k * n')) * (ζ⁻¹) ^ (k * n) =
      ∑ n' ∈ range N, f n' * (ζ ^ n' * (ζ⁻¹) ^ n) ^ k := by
    intro k _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun n' _ => ?_
    rw [mul_pow, mul_comm k n', pow_mul, mul_comm k n, pow_mul]
    ring
  rw [Finset.sum_congr rfl hexpand, Finset.sum_comm]
  have hinner : ∀ n' ∈ range N,
      ∑ k ∈ range N, f n' * (ζ ^ n' * (ζ⁻¹) ^ n) ^ k =
      f n' * (if n' = n then (N : F) else 0) := by
    intro n' hn'
    rw [← Finset.mul_sum, sum_pow_mul_inv_pow_eq_ite hζ hN n' n]
    congr 1
    rw [Nat.mod_eq_of_lt (Finset.mem_range.mp hn'), Nat.mod_eq_of_lt hn]
  rw [Finset.sum_congr rfl hinner]
  have hcollapse : ∀ n' ∈ range N,
      f n' * (if n' = n then (N : F) else 0) =
      (if n' = n then (N : F) * f n' else 0) := by
    intro n' _
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hcollapse,
    Finset.sum_ite_eq' (range N) n (fun n' => (N : F) * f n'),
    if_pos (Finset.mem_range.mpr hn)]

/-- **The atlas's root-of-unity formula for the individual sign**: over
`ℂ` with `ζ = e^(2πi/2^m)`, the inverse transform of the dyadic DFT
`ε̂(k) = ∑_{n'} ε(n')·ζ^(-k·n')` recovers `2^m·ε(n)` on the block. -/
theorem thueMorse_dft_inversion (m n : ℕ) (hn : n < 2 ^ m) :
    ∑ k ∈ range (2 ^ m),
        (∑ n' ∈ range (2 ^ m), ((thueMorseSign n' : ℤ) : ℂ) *
            Complex.exp (2 * Real.pi * Complex.I / (2 ^ m)) ^ (k * n')) *
          ((Complex.exp (2 * Real.pi * Complex.I / (2 ^ m)))⁻¹) ^ (k * n) =
      ((2 ^ m : ℕ) : ℂ) * ((thueMorseSign n : ℤ) : ℂ) := by
  have hprim : IsPrimitiveRoot
      (Complex.exp (2 * Real.pi * Complex.I / (2 ^ m))) (2 ^ m) := by
    have h := Complex.isPrimitiveRoot_exp (2 ^ m) (Nat.two_pow_pos m).ne'
    convert h using 2
    push_cast
    ring
  exact dft_inversion hprim (Nat.two_pow_pos m).ne'
    (fun n' => ((thueMorseSign n' : ℤ) : ℂ)) n hn

end Fabius
