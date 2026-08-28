import FabiusFunction.FourierLaplaceRotation
import FabiusFunction.LacunaryProductToSum
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The centered Rvachev Fourier prefix as a Thue--Morse polynomial

At the dyadically dilated real argument `2^(m+1) w`, the first `m+1`
factors of the centered sinc product are, in reverse order,

`sinc (2^m w), sinc (2^(m-1) w), ..., sinc w`.

Clearing their removable denominators and using the lacunary
product-to-sum theorem therefore gives the exact, total identity

`2^(m + (m+1).choose 2) w^(m+1) Q_{m+1}(2^(m+1)w)
  = T_m(w)`,

where `T_m` is the odd-frequency Thue--Morse sine polynomial.  No
division by `w` occurs, so the formula includes `w = 0`.

The normalization `Q(z) = Phi(z / (2*pi))` and the centered shell law
then turn the finite identity into the full Fourier-image bridge

`2^(m + (m+1).choose 2) w^(m+1) Phi(2^m w / pi)
  = T_m(w) Phi(w / (2*pi))`.

The public product form of `T_m` also makes its removable zero, its parity,
and its complete factor-level zero criterion available without reopening the
trigonometric sum.

Thus the Thue--Morse polynomial is exactly the new finite shell acquired
by the Rvachev Fourier image under a dyadic dilation.  The final zero
criteria record the corresponding finite and infinite statements: away
from the removable point `w = 0`, the centered prefix vanishes exactly when
the Thue--Morse sine polynomial does, while the full Fourier image vanishes
exactly when either that finite shell or the remaining tail vanishes.
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Fabius

noncomputable section

/-- The odd-frequency Thue--Morse sine polynomial appearing in the
lacunary product-to-sum identity. -/
noncomputable def thueMorseSinePolynomial (m : ℕ) (w : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (2 ^ m),
    (thueMorseSign n : ℝ) *
      Real.sin ((m : ℝ) * Real.pi / 2 + (2 * n + 1) * w)

/-- The conceptual form of the Thue--Morse sine polynomial: it is precisely
the cleared lacunary sine product.  Keeping this formulation public avoids
reopening the frequency-sum definition in downstream Fourier arguments. -/
theorem thueMorseSinePolynomial_eq_prod_sin_two_pow (m : ℕ) (w : ℝ) :
    thueMorseSinePolynomial m w =
      (2 : ℝ) ^ m *
        ∏ j ∈ Finset.range (m + 1), Real.sin ((2 : ℝ) ^ j * w) := by
  simpa [thueMorseSinePolynomial] using
    (prod_sin_two_pow_eq_thueMorse_sum m w).symm

/-- The Thue--Morse sine shell always has the expected removable zero at the
origin. -/
@[simp] theorem thueMorseSinePolynomial_zero (m : ℕ) :
    thueMorseSinePolynomial m 0 = 0 := by
  rw [thueMorseSinePolynomial_eq_prod_sin_two_pow]
  apply mul_eq_zero_of_right
  refine Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.zero_lt_succ m)) ?_
  simp

/-- The shell has the parity of a product of `m + 1` odd functions. -/
theorem thueMorseSinePolynomial_neg (m : ℕ) (w : ℝ) :
    thueMorseSinePolynomial m (-w) =
      (-1 : ℝ) ^ (m + 1) * thueMorseSinePolynomial m w := by
  rw [thueMorseSinePolynomial_eq_prod_sin_two_pow,
    thueMorseSinePolynomial_eq_prod_sin_two_pow]
  have hprod :
      (∏ j ∈ Finset.range (m + 1), Real.sin ((2 : ℝ) ^ j * -w)) =
        (-1 : ℝ) ^ (m + 1) *
          ∏ j ∈ Finset.range (m + 1), Real.sin ((2 : ℝ) ^ j * w) := by
    calc
      (∏ j ∈ Finset.range (m + 1), Real.sin ((2 : ℝ) ^ j * -w)) =
          ∏ j ∈ Finset.range (m + 1),
            -Real.sin ((2 : ℝ) ^ j * w) := by
        apply Finset.prod_congr rfl
        intro j _hj
        rw [show (2 : ℝ) ^ j * -w = -((2 : ℝ) ^ j * w) by ring,
          Real.sin_neg]
      _ = (-1 : ℝ) ^ (m + 1) *
          ∏ j ∈ Finset.range (m + 1), Real.sin ((2 : ℝ) ^ j * w) := by
        rw [Finset.prod_neg, Finset.card_range]
  rw [hprod]
  ring

/-- The zero set of the Thue--Morse shell is exactly the union of the zero
sets of its lacunary sine factors. -/
theorem thueMorseSinePolynomial_eq_zero_iff (m : ℕ) (w : ℝ) :
    thueMorseSinePolynomial m w = 0 ↔
      ∃ j < m + 1, Real.sin ((2 : ℝ) ^ j * w) = 0 := by
  rw [thueMorseSinePolynomial_eq_prod_sin_two_pow]
  constructor
  · intro hzero
    have hprod :
        ∏ j ∈ Finset.range (m + 1), Real.sin ((2 : ℝ) ^ j * w) = 0 :=
      (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero _ (by norm_num))
    rw [Finset.prod_eq_zero_iff] at hprod
    rcases hprod with ⟨j, hj, hsin⟩
    exact ⟨j, Finset.mem_range.mp hj, hsin⟩
  · rintro ⟨j, hj, hsin⟩
    apply mul_eq_zero_of_right
    rw [Finset.prod_eq_zero_iff]
    exact ⟨j, Finset.mem_range.mpr hj, hsin⟩

/-- Multiplication by the real argument clears `complexSinc` even at its
removable value at zero. -/
private theorem ofReal_mul_complexSinc (r : ℝ) :
    (r : ℂ) * complexSinc (r : ℂ) = (Real.sin r : ℂ) := by
  by_cases hr : r = 0
  · subst r
    simp [complexSinc]
  · rw [complexSinc, if_neg (Complex.ofReal_ne_zero.mpr hr),
      ← Complex.ofReal_sin]
    field_simp [Complex.ofReal_ne_zero.mpr hr]
    <;> ring

/-- At a dyadic dilation, the centered prefix is the ascending lacunary
sinc product, written in the reverse of its defining order. -/
private theorem centeredSincPartialProduct_dyadic_prefix
    (m : ℕ) (w : ℝ) :
    centeredSincPartialProduct
        ((2 : ℂ) ^ (m + 1) * (w : ℂ)) (m + 1) =
      ∏ j ∈ Finset.range (m + 1),
        complexSinc ((((2 : ℝ) ^ j * w : ℝ) : ℂ)) := by
  unfold centeredSincPartialProduct
  rw [← Finset.prod_range_reflect
    (fun j => complexSinc ((((2 : ℝ) ^ j * w : ℝ) : ℂ))) (m + 1)]
  apply Finset.prod_congr rfl
  intro j hj
  have hjle : j ≤ m := by
    have hjlt := Finset.mem_range.mp hj
    omega
  have hindex : m + 1 - 1 - j = m - j := by omega
  rw [hindex]
  congr 1
  push_cast
  have hsplit :
      (2 : ℂ) ^ (m + 1) =
        (2 : ℂ) ^ (m - j) * (2 : ℂ) ^ (j + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit]
  field_simp
  <;> ring

/-- Clearing the denominators of the centered dyadic prefix leaves the
plain lacunary sine product. -/
private theorem centeredSincPartialProduct_dyadic_clear
    (m : ℕ) (w : ℝ) :
    ((2 : ℂ) ^ ((m + 1).choose 2) * (w : ℂ) ^ (m + 1)) *
        centeredSincPartialProduct
          ((2 : ℂ) ^ (m + 1) * (w : ℂ)) (m + 1) =
      ∏ j ∈ Finset.range (m + 1),
        (Real.sin ((2 : ℝ) ^ j * w) : ℂ) := by
  rw [centeredSincPartialProduct_dyadic_prefix]
  have hden :
      (∏ j ∈ Finset.range (m + 1),
          ((((2 : ℝ) ^ j * w : ℝ) : ℂ))) =
        (2 : ℂ) ^ ((m + 1).choose 2) * (w : ℂ) ^ (m + 1) := by
    push_cast
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
      Finset.prod_pow_eq_pow_sum, Finset.sum_range_id,
      Nat.choose_two_right]
  calc
    ((2 : ℂ) ^ ((m + 1).choose 2) * (w : ℂ) ^ (m + 1)) *
          (∏ j ∈ Finset.range (m + 1),
            complexSinc ((((2 : ℝ) ^ j * w : ℝ) : ℂ))) =
        (∏ j ∈ Finset.range (m + 1),
            ((((2 : ℝ) ^ j * w : ℝ) : ℂ))) *
          (∏ j ∈ Finset.range (m + 1),
            complexSinc ((((2 : ℝ) ^ j * w : ℝ) : ℂ))) := by
          rw [hden]
    _ = ∏ j ∈ Finset.range (m + 1),
          ((((2 : ℝ) ^ j * w : ℝ) : ℂ) *
            complexSinc ((((2 : ℝ) ^ j * w : ℝ) : ℂ))) := by
          rw [Finset.prod_mul_distrib]
    _ = ∏ j ∈ Finset.range (m + 1),
          (Real.sin ((2 : ℝ) ^ j * w) : ℂ) := by
          apply Finset.prod_congr rfl
          intro j _hj
          exact ofReal_mul_complexSinc ((2 : ℝ) ^ j * w)

/-- **Centered finite Fourier prefix = Thue--Morse sine polynomial.**

This is the exact cross-multiplied formula

`2^(m + (m+1).choose 2) w^(m+1) Q_{m+1}(2^(m+1)w) = T_m(w)`.

It is valid at `w = 0`; the removable sinc singularities have already
been cleared before the product-to-sum identity is applied. -/
theorem centeredSincPartialProduct_dyadic_eq_thueMorse
    (m : ℕ) (w : ℝ) :
    ((2 : ℂ) ^ (m + (m + 1).choose 2) * (w : ℂ) ^ (m + 1)) *
        centeredSincPartialProduct
          ((2 : ℂ) ^ (m + 1) * (w : ℂ)) (m + 1) =
      (thueMorseSinePolynomial m w : ℂ) := by
  have hclear := centeredSincPartialProduct_dyadic_clear m w
  have htmC := congrArg (fun r : ℝ => (r : ℂ))
    (thueMorseSinePolynomial_eq_prod_sin_two_pow m w).symm
  push_cast at htmC
  calc
    ((2 : ℂ) ^ (m + (m + 1).choose 2) * (w : ℂ) ^ (m + 1)) *
          centeredSincPartialProduct
            ((2 : ℂ) ^ (m + 1) * (w : ℂ)) (m + 1) =
        (2 : ℂ) ^ m *
          (((2 : ℂ) ^ ((m + 1).choose 2) * (w : ℂ) ^ (m + 1)) *
            centeredSincPartialProduct
              ((2 : ℂ) ^ (m + 1) * (w : ℂ)) (m + 1)) := by
          rw [pow_add]
          ring
    _ = (2 : ℂ) ^ m *
        (∏ j ∈ Finset.range (m + 1),
          (Real.sin ((2 : ℝ) ^ j * w) : ℂ)) := by rw [hclear]
    _ = (thueMorseSinePolynomial m w : ℂ) := htmC

/-- **The finite zero criterion.**  Away from the removable point `w = 0`,
the centered Fourier prefix vanishes exactly at the zeros of its associated
Thue--Morse sine polynomial. -/
theorem centeredSincPartialProduct_dyadic_eq_zero_iff
    (m : ℕ) {w : ℝ} (hw : w ≠ 0) :
    centeredSincPartialProduct
        ((2 : ℂ) ^ (m + 1) * (w : ℂ)) (m + 1) = 0 ↔
      thueMorseSinePolynomial m w = 0 := by
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have hwC : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw
  have hcoefficient :
      (2 : ℂ) ^ (m + (m + 1).choose 2) * (w : ℂ) ^ (m + 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ htwo) (pow_ne_zero _ hwC)
  constructor
  · intro hp
    have hzero : (thueMorseSinePolynomial m w : ℂ) = 0 := by
      rw [← centeredSincPartialProduct_dyadic_eq_thueMorse m w, hp,
        mul_zero]
    exact_mod_cast hzero
  · intro htm
    have htmC : (thueMorseSinePolynomial m w : ℂ) = 0 := by
      exact_mod_cast htm
    have hzero :
        ((2 : ℂ) ^ (m + (m + 1).choose 2) * (w : ℂ) ^ (m + 1)) *
          centeredSincPartialProduct
            ((2 : ℂ) ^ (m + 1) * (w : ℂ)) (m + 1) = 0 := by
      calc
        ((2 : ℂ) ^ (m + (m + 1).choose 2) * (w : ℂ) ^ (m + 1)) *
            centeredSincPartialProduct
              ((2 : ℂ) ^ (m + 1) * (w : ℂ)) (m + 1) =
          (thueMorseSinePolynomial m w : ℂ) :=
            centeredSincPartialProduct_dyadic_eq_thueMorse m w
        _ = 0 := htmC
    exact (mul_eq_zero.mp hzero).resolve_left hcoefficient

/-- Factor-level form of the finite zero criterion.  Away from `w = 0`, the
dyadic sinc prefix vanishes precisely when one of the exposed lacunary sine
factors vanishes. -/
theorem centeredSincPartialProduct_dyadic_eq_zero_iff_exists
    (m : ℕ) {w : ℝ} (hw : w ≠ 0) :
    centeredSincPartialProduct
        ((2 : ℂ) ^ (m + 1) * (w : ℂ)) (m + 1) = 0 ↔
      ∃ j < m + 1, Real.sin ((2 : ℝ) ^ j * w) = 0 := by
  rw [centeredSincPartialProduct_dyadic_eq_zero_iff m hw,
    thueMorseSinePolynomial_eq_zero_iff]

/-- **The exact Rvachev Fourier-image bridge.**  The Thue--Morse
polynomial is precisely the finite shell acquired when the Fourier image is
dilated from `w / (2*pi)` to `2^m w / pi`:

`2^(m + (m+1).choose 2) w^(m+1) Phi(2^m w / pi)
  = T_m(w) Phi(w / (2*pi))`.

The identity is algebraic and total.  Its only analytic input is the already
proved centered shell factorization of the convergent sinc product. -/
theorem rvachevFourierProduct_dyadic_eq_thueMorse
    (m : ℕ) (w : ℝ) :
    ((2 : ℂ) ^ (m + (m + 1).choose 2) * (w : ℂ) ^ (m + 1)) *
        rvachevFourierProduct
          ((2 : ℂ) ^ m * (w : ℂ) / (Real.pi : ℂ)) =
      (thueMorseSinePolynomial m w : ℂ) *
        rvachevFourierProduct
          ((w : ℂ) / (2 * (Real.pi : ℂ))) := by
  let z : ℂ := (2 : ℂ) ^ (m + 1) * (w : ℂ)
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hhigh :
      z / (2 * (Real.pi : ℂ)) =
        (2 : ℂ) ^ m * (w : ℂ) / (Real.pi : ℂ) := by
    dsimp [z]
    rw [pow_succ]
    field_simp [hpi]
    <;> ring
  have htail : z / (2 : ℂ) ^ (m + 1) = (w : ℂ) := by
    dsimp [z]
    field_simp
    <;> ring
  have hshell :
      centeredSincProduct z =
        centeredSincPartialProduct z (m + 1) *
          centeredSincProduct (w : ℂ) := by
    rw [centeredSincProduct_shell, htail]
  have hhighProduct :
      centeredSincProduct z =
        rvachevFourierProduct
          ((2 : ℂ) ^ m * (w : ℂ) / (Real.pi : ℂ)) := by
    rw [centeredSincProduct_eq_rvachevFourierProduct, hhigh]
  calc
    ((2 : ℂ) ^ (m + (m + 1).choose 2) * (w : ℂ) ^ (m + 1)) *
          rvachevFourierProduct
            ((2 : ℂ) ^ m * (w : ℂ) / (Real.pi : ℂ)) =
        ((2 : ℂ) ^ (m + (m + 1).choose 2) * (w : ℂ) ^ (m + 1)) *
          centeredSincProduct z := by rw [hhighProduct]
    _ = ((2 : ℂ) ^ (m + (m + 1).choose 2) * (w : ℂ) ^ (m + 1)) *
          (centeredSincPartialProduct z (m + 1) *
            centeredSincProduct (w : ℂ)) := by rw [hshell]
    _ = (((2 : ℂ) ^ (m + (m + 1).choose 2) * (w : ℂ) ^ (m + 1)) *
          centeredSincPartialProduct z (m + 1)) *
            centeredSincProduct (w : ℂ) := by ring
    _ = (thueMorseSinePolynomial m w : ℂ) *
          centeredSincProduct (w : ℂ) := by
        rw [show z = (2 : ℂ) ^ (m + 1) * (w : ℂ) by rfl,
          centeredSincPartialProduct_dyadic_eq_thueMorse]
    _ = (thueMorseSinePolynomial m w : ℂ) *
        rvachevFourierProduct
          ((w : ℂ) / (2 * (Real.pi : ℂ))) := by
      rw [centeredSincProduct_eq_rvachevFourierProduct]

/-- **Zero transfer across a dyadic Fourier shell.**  Away from `w = 0`, a
zero at the dilated argument comes either from the newly exposed
Thue--Morse shell or from the undilated tail, and these are the only two
possibilities. -/
theorem rvachevFourierProduct_dyadic_eq_zero_iff
    (m : ℕ) {w : ℝ} (hw : w ≠ 0) :
    rvachevFourierProduct
        ((2 : ℂ) ^ m * (w : ℂ) / (Real.pi : ℂ)) = 0 ↔
      thueMorseSinePolynomial m w = 0 ∨
        rvachevFourierProduct
          ((w : ℂ) / (2 * (Real.pi : ℂ))) = 0 := by
  have hcoefficient :
      (2 : ℂ) ^ (m + (m + 1).choose 2) * (w : ℂ) ^ (m + 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num))
      (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hw))
  constructor
  · intro hhigh
    have hshell :
        (thueMorseSinePolynomial m w : ℂ) *
            rvachevFourierProduct
              ((w : ℂ) / (2 * (Real.pi : ℂ))) = 0 := by
      rw [← rvachevFourierProduct_dyadic_eq_thueMorse m w, hhigh,
        mul_zero]
    rcases mul_eq_zero.mp hshell with htm | htail
    · left
      exact_mod_cast htm
    · exact Or.inr htail
  · intro hzero
    have hshell :
        (thueMorseSinePolynomial m w : ℂ) *
            rvachevFourierProduct
              ((w : ℂ) / (2 * (Real.pi : ℂ))) = 0 := by
      rcases hzero with htm | htail
      · have htmC : (thueMorseSinePolynomial m w : ℂ) = 0 := by
          exact_mod_cast htm
        rw [htmC, zero_mul]
      · rw [htail, mul_zero]
    have hscaled :
        ((2 : ℂ) ^ (m + (m + 1).choose 2) * (w : ℂ) ^ (m + 1)) *
            rvachevFourierProduct
              ((2 : ℂ) ^ m * (w : ℂ) / (Real.pi : ℂ)) = 0 := by
      rw [rvachevFourierProduct_dyadic_eq_thueMorse]
      exact hshell
    exact (mul_eq_zero.mp hscaled).resolve_left hcoefficient

end

end Fabius
