import FabiusFunction.LacunaryProductToSum

/-!
# The cosine companion of the lacunary product-to-sum identity

The sine identity of `LacunaryProductToSum` reads

`2ᵐ ∏_{j≤m} sin(2ʲw) = ∑_{n<2ᵐ} εₙ sin(mπ/2 + (2n+1)w)`.

Replacing the affine phase `φ` by `φ + π/2` in the upstream affine
factorization turns every sine into a cosine on both sides, and the
top factor `sin(2ᵐw)` of the lacunary product into `cos(2ᵐw)`:

`2ᵐ·cos(2ᵐw)·∏_{j<m} sin(2ʲw) = ∑_{n<2ᵐ} εₙ cos(mπ/2 + (2n+1)w)`.

Rescaled by `w = z/2ᵐ` this is the atlas's cosine companion

`2ᵐ·cos z·∏_{r=1}^{m} sin(z/2ʳ) = ∑_{n<2ᵐ} εₙ cos(mπ/2 + (2n+1)z/2ᵐ)`,

the form in which the cosine factor of a shell decomposition meets
the same Thue–Morse coefficient word as the sine factor.

* `sum_thueMorseSign_mul_cos_affine` — the affine cosine
  factorization, the `φ + π/2` shift of the sine one;
* `prod_sin_two_pow_mul_cos_eq_thueMorse_sum` — **the identity**;
* `prod_sin_inv_two_pow_mul_cos_eq_thueMorse_sum` — its `z`-form.
-/

set_option autoImplicit false

open Finset Real

namespace Fabius

/-- **The affine cosine factorization**: shifting the phase of
`sum_thueMorseSign_mul_sin_affine` by a quarter turn. -/
theorem sum_thueMorseSign_mul_cos_affine (x φ : ℝ) (m : ℕ) :
    ∑ n ∈ range (2 ^ m),
        (thueMorseSign n : ℝ) * Real.cos (φ + (n : ℝ) * x) =
      (2 : ℝ) ^ m * (∏ j ∈ range m, Real.sin (2 ^ j * x / 2)) *
        Real.cos
          (φ + ((2 ^ m - 1 : ℕ) : ℝ) * x / 2 -
            (m : ℝ) * Real.pi / 2) := by
  have hshift := sum_thueMorseSign_mul_sin_affine x (φ + π / 2) m
  have hleft : (∑ n ∈ range (2 ^ m),
      (thueMorseSign n : ℝ) *
        Real.sin (φ + π / 2 + (n : ℝ) * x)) =
      ∑ n ∈ range (2 ^ m),
        (thueMorseSign n : ℝ) * Real.cos (φ + (n : ℝ) * x) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    rw [show φ + π / 2 + (n : ℝ) * x = (φ + (n : ℝ) * x) + π / 2 by
      ring, Real.sin_add_pi_div_two]
  have hright : Real.sin
      (φ + π / 2 + ((2 ^ m - 1 : ℕ) : ℝ) * x / 2 -
        (m : ℝ) * Real.pi / 2) =
      Real.cos
        (φ + ((2 ^ m - 1 : ℕ) : ℝ) * x / 2 -
          (m : ℝ) * Real.pi / 2) := by
    rw [show φ + π / 2 + ((2 ^ m - 1 : ℕ) : ℝ) * x / 2 -
        (m : ℝ) * Real.pi / 2 =
        (φ + ((2 ^ m - 1 : ℕ) : ℝ) * x / 2 -
          (m : ℝ) * Real.pi / 2) + π / 2 by ring,
      Real.sin_add_pi_div_two]
  rw [hleft, hright] at hshift
  exact hshift

/-- **The cosine companion**: the lacunary sine product with its top
factor replaced by a cosine is the Thue–Morse *cosine* polynomial at
the same odd frequencies —
`2ᵐ·cos(2ᵐw)·∏_{j<m} sin(2ʲw) = ∑_{n<2ᵐ} εₙ cos(mπ/2 + (2n+1)w)`. -/
theorem prod_sin_two_pow_mul_cos_eq_thueMorse_sum (m : ℕ) (w : ℝ) :
    (2 : ℝ) ^ m * Real.cos ((2 : ℝ) ^ m * w) *
        ∏ j ∈ Finset.range m, Real.sin (2 ^ j * w) =
      ∑ n ∈ Finset.range (2 ^ m),
        (thueMorseSign n : ℝ) *
          Real.cos ((m : ℝ) * π / 2 + (2 * n + 1) * w) := by
  have hsum :
      (∑ n ∈ Finset.range (2 ^ m),
        (thueMorseSign n : ℝ) *
          Real.cos ((m : ℝ) * π / 2 + (2 * n + 1) * w)) =
        ∑ n ∈ Finset.range (2 ^ m),
          (thueMorseSign n : ℝ) *
            Real.cos (((m : ℝ) * π / 2 + w) + (n : ℝ) * (2 * w)) := by
    apply Finset.sum_congr rfl
    intro n _
    congr 1
    ring_nf
  have hproduct :
      (∏ j ∈ Finset.range m, Real.sin (2 ^ j * (2 * w) / 2)) =
        ∏ j ∈ Finset.range m, Real.sin (2 ^ j * w) := by
    apply Finset.prod_congr rfl
    intro j _
    congr 1
    ring
  have hphase :
      ((m : ℝ) * π / 2 + w) +
          ((2 ^ m - 1 : ℕ) : ℝ) * (2 * w) / 2 -
          (m : ℝ) * π / 2 =
        (2 : ℝ) ^ m * w := by
    have hone : (1 : ℕ) ≤ 2 ^ m := Nat.one_le_two_pow
    push_cast [Nat.cast_sub hone]
    ring
  have haffine :=
    sum_thueMorseSign_mul_cos_affine
      (2 * w) ((m : ℝ) * π / 2 + w) m
  rw [hproduct, hphase] at haffine
  rw [hsum, haffine]
  ring

/-- The `z`-form of the cosine companion: with `w = z/2ᵐ` the top
factor is `cos z` and the product runs over the negative dyadic
scales, `∏_{j<m} sin(z/2^{m-j})`. -/
theorem prod_sin_inv_two_pow_mul_cos_eq_thueMorse_sum (m : ℕ)
    (z : ℝ) :
    (2 : ℝ) ^ m * Real.cos z *
        ∏ j ∈ Finset.range m,
          Real.sin (2 ^ j * (z / (2 : ℝ) ^ m)) =
      ∑ n ∈ Finset.range (2 ^ m),
        (thueMorseSign n : ℝ) *
          Real.cos ((m : ℝ) * π / 2 +
            (2 * n + 1) * (z / (2 : ℝ) ^ m)) := by
  have h := prod_sin_two_pow_mul_cos_eq_thueMorse_sum m
    (z / (2 : ℝ) ^ m)
  have htop : (2 : ℝ) ^ m * (z / (2 : ℝ) ^ m) = z := by
    field_simp
  rw [htop] at h
  exact h

end Fabius
