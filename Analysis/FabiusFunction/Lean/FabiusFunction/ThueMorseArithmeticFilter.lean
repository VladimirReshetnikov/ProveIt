import FabiusFunction.ThueMorseFourierInversion
import FabiusFunction.ThueMorseEulerTransform

/-!
# The root-of-unity filter for rarefied Thue–Morse sums

Averaging characters over a full period extracts an arithmetic
progression: `(1/q)·∑_{ℓ<q} ζ^((n-r)ℓ) = [n ≡ r (mod q)]` for a
primitive `q`-th root of unity `ζ`.  Applied to the Thue–Morse block
polynomial this yields the atlas's exact finite formula for the
rarefied partial sums — the entry point to Newman's phenomenon.

* `sum_filter_modEq_mul_natCast` — the **general filter**, over any
  field and any coefficient function `f`:
  `q·∑_{n<N, n≡r (q)} f(n) = ∑_{ℓ<q} (ζ⁻¹)^(rℓ)·∑_{n<N} f(n)ζ^(nℓ)`.
* `thueMorse_rarefied_filter` — the specialization
  `q·A_{m,r}^{(q)} = ∑_{ℓ<q} ζ_q^(-rℓ)·∏_{j<m}(1-ζ_q^(ℓ·2^j))`
  over `ℂ`, with the transform written as the finite product.
* `sum_thueMorseSign_even_range` — the even-modulus collapse
  `A_{m,0}^{(2)} = 0` for `m ≥ 2`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

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

/-- **The rarefied filter formula** (the atlas's boxed identity): with
`ζ_q = e^(2πi/q)`,
`q·A_{m,r}^{(q)} = ∑_{ℓ<q} ζ_q^(-rℓ)·∏_{j<m}(1 - ζ_q^(ℓ·2^j))` —
each twisted transform of the Thue–Morse block collapses to the finite
product. -/
theorem thueMorse_rarefied_filter (q : ℕ) (hq : q ≠ 0) (m r : ℕ) :
    (q : ℂ) * ∑ n ∈ (range (2 ^ m)).filter (fun n => n % q = r % q),
        ((thueMorseSign n : ℤ) : ℂ) =
      ∑ ℓ ∈ range q,
        ((Complex.exp (2 * Real.pi * Complex.I / q))⁻¹) ^ (r * ℓ) *
          ∏ j ∈ range m,
            (1 - Complex.exp (2 * Real.pi * Complex.I / q) ^ (ℓ * 2 ^ j)) := by
  have hprim : IsPrimitiveRoot
      (Complex.exp (2 * Real.pi * Complex.I / q)) q :=
    Complex.isPrimitiveRoot_exp q hq
  rw [sum_filter_modEq_mul_natCast hprim hq]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  congr 1
  calc ∑ n ∈ range (2 ^ m), ((thueMorseSign n : ℤ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I / q) ^ (n * ℓ)
      = ∑ n ∈ range (2 ^ m), ((thueMorseSign n : ℤ) : ℂ) *
          (Complex.exp (2 * Real.pi * Complex.I / q) ^ ℓ) ^ n := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [← pow_mul, mul_comm ℓ n]
    _ = ∏ j ∈ range m,
          (1 - (Complex.exp (2 * Real.pi * Complex.I / q) ^ ℓ) ^ (2 ^ j)) :=
        (prod_one_sub_pow_eq_sum_thueMorseSign _ m).symm
    _ = ∏ j ∈ range m,
          (1 - Complex.exp (2 * Real.pi * Complex.I / q) ^ (ℓ * 2 ^ j)) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [← pow_mul]

/-- **Even-modulus collapse**: the even rarefied sum vanishes,
`A_{m,0}^{(2)} = ∑_{n<2^m, n even} ε(n) = 0` for `m ≥ 2` — halving the
index halves the block, whose signed sum is zero. -/
theorem sum_thueMorseSign_even_range (m : ℕ) (hm : 2 ≤ m) :
    ∑ n ∈ (range (2 ^ m)).filter (fun n => n % 2 = 0),
        thueMorseSign n = 0 := by
  have himg : (range (2 ^ m)).filter (fun n => n % 2 = 0) =
      (range (2 ^ (m - 1))).image (fun k => 2 * k) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hn, hpar⟩
      refine ⟨n / 2, ?_, by omega⟩
      have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      omega
    · rintro ⟨k, hk, rfl⟩
      have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      omega
  rw [himg, Finset.sum_image (fun a _ b _ h => by omega)]
  have hdouble : ∀ k ∈ range (2 ^ (m - 1)),
      thueMorseSign (2 * k) = thueMorseSign k := by
    intro k _
    exact thueMorseSign_two_mul k
  rw [Finset.sum_congr rfl hdouble, sum_thueMorseSign_range]
  rw [if_pos (dvd_pow_self 2 (by omega : m - 1 ≠ 0))]

end Fabius
