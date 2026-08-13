import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Arbitrary-degree Fourier reconstruction in Lazard's convention

This file formalizes the formula-independent Fourier core used in Section 2
of Lazard's paper.  Indices live in `ZMod d`; a primitive additive character
plays the role of the powers of a primitive `d`th root of unity.

The forward transform has Lazard's positive-exponent convention

`s k = \sum j, psi (j * k) * x j`,

and the inverse therefore has the negative exponent.  Fourier inversion needs
both a positive degree (`[NeZero d]`) and the honest characteristic condition
`(d : K) != 0`, because it divides by `d`.

This module deliberately stops at character orthogonality, cyclic-shift
covariance, and Fourier inversion.  Recovering modes from Lazard's invariant
coordinates requires a compatible choice of a `d`th root and is a separate,
branch-sensitive theorem.
-/

namespace LeanProofs.PolynomialFormulas.LazardGeneralFourier

set_option autoImplicit false

open scoped BigOperators

variable {d : ℕ} [NeZero d] {K : Type*} [Field K]

/-- Lazard's forward discrete Fourier transform, with positive exponent. -/
def dft (ψ : AddChar (ZMod d) K) (x : ZMod d → K) (k : ZMod d) : K :=
  ∑ j : ZMod d, ψ (j * k) * x j

/-- The inverse transform corresponding to `dft`.

The factor `(d : K)⁻¹` is meaningful for inversion only under the explicit
hypothesis `(d : K) ≠ 0` used by `invDFT_dft` below. -/
def invDFT (ψ : AddChar (ZMod d) K) (s : ZMod d → K) (i : ZMod d) : K :=
  (d : K)⁻¹ * ∑ k : ZMod d, ψ (-(i * k)) * s k

/-- The cyclic relabelling `x_i ↦ x_{i-a}`. -/
def shift (a : ZMod d) (x : ZMod d → K) (i : ZMod d) : K :=
  x (i - a)

/-- A primitive additive character has the usual finite geometric-sum
orthogonality relation. -/
theorem character_orthogonality (ψ : AddChar (ZMod d) K)
    (hψ : ψ.IsPrimitive) (b : ZMod d) :
    ∑ j : ZMod d, ψ (j * b) = if b = 0 then (d : K) else 0 := by
  simpa [ZMod.card] using
    (AddChar.sum_mulShift (R := ZMod d) (R' := K) b hψ)

/-- Under the cyclic relabelling `x_i ↦ x_{i-a}`, Fourier mode `k` is
multiplied by `ψ (a*k)`. -/
theorem dft_shift (ψ : AddChar (ZMod d) K) (x : ZMod d → K)
    (a k : ZMod d) :
    dft ψ (shift a x) k = ψ (a * k) * dft ψ x k := by
  unfold dft shift
  calc
    (∑ j : ZMod d, ψ (j * k) * x (j - a)) =
        ∑ j : ZMod d, ψ ((a + j) * k) * x j := by
      exact Fintype.sum_equiv (Equiv.addLeft (-a)) _ _ fun j ↦ by
        simp [sub_eq_add_neg, add_comm]
    _ = ψ (a * k) * ∑ j : ZMod d, ψ (j * k) * x j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [add_mul, ψ.map_add_eq_mul, mul_assoc]

/-- Orthogonality in the exact sign pattern that occurs when composing the
inverse transform with the forward transform. -/
private theorem inverse_kernel_sum (ψ : AddChar (ZMod d) K)
    (hψ : ψ.IsPrimitive) (i j : ZMod d) :
    ∑ k : ZMod d, ψ (-(i * k)) * ψ (j * k) =
      if j = i then (d : K) else 0 := by
  calc
    (∑ k : ZMod d, ψ (-(i * k)) * ψ (j * k)) =
        ∑ k : ZMod d, ψ (k * (j - i)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← ψ.map_add_eq_mul]
      congr 1
      calc
        -(i * k) + j * k = j * k + -(i * k) := add_comm _ _
        _ = k * j + -(k * i) := by rw [mul_comm j k, mul_comm i k]
        _ = k * j - k * i := (sub_eq_add_neg _ _).symm
        _ = k * (j - i) := (mul_sub k j i).symm
    _ = if j - i = 0 then (d : K) else 0 :=
      character_orthogonality ψ hψ (j - i)
    _ = if j = i then (d : K) else 0 := by simp only [sub_eq_zero]

/-- Fourier inversion over an arbitrary field.  The nonzero cast of `d` is
the precise condition needed to cancel the normalization factor; in
particular, arbitrary degree cannot be treated uniformly in characteristic
dividing `d`. -/
theorem invDFT_dft (ψ : AddChar (ZMod d) K) (hψ : ψ.IsPrimitive)
    (hd : (d : K) ≠ 0) (x : ZMod d → K) :
    invDFT ψ (dft ψ x) = x := by
  funext i
  unfold invDFT dft
  calc
    (d : K)⁻¹ *
          ∑ k : ZMod d, ψ (-(i * k)) *
            (∑ j : ZMod d, ψ (j * k) * x j) =
        (d : K)⁻¹ *
          ∑ j : ZMod d,
            (∑ k : ZMod d, ψ (-(i * k)) * ψ (j * k)) * x j := by
      congr 1
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [← mul_assoc, Finset.sum_mul]
    _ = (d : K)⁻¹ *
          ∑ j : ZMod d, (if j = i then (d : K) else 0) * x j := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [inverse_kernel_sum ψ hψ i j]
    _ = (d : K)⁻¹ * ((d : K) * x i) := by simp
    _ = x i := by rw [← mul_assoc, inv_mul_cancel₀ hd, one_mul]

end LeanProofs.PolynomialFormulas.LazardGeneralFourier
