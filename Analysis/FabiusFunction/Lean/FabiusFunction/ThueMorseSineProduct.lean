import FabiusFunction.ThueMorseComplexHalfAngle
import FabiusFunction.ThueMorseFourier
import FabiusFunction.ThueMorseWalsh

/-!
# The sine-product form of the Thue–Morse trigonometric polynomial

Factoring each `1 - e^(i·2^j x)` through the half-angle identity turns
the signed block sum on the unit circle into an explicit product of
sines times a single phase — the closed form behind the dyadic discrete
Fourier transform.

The first two results are the real specializations of the hypothesis-free
complex identities of `ThueMorseComplexHalfAngle`: setting `z = (x : ℂ)`
and moving the coercion through `Complex.ofReal_sin` is all that is
needed, so only the cast bookkeeping is done here.

* `one_sub_exp_mul_I` — the **half-angle factorization**
  `1 - e^(iv) = -2i·e^(iv/2)·sin(v/2)`, by pure exponential algebra.
* `sum_thueMorseSign_exp_eq_sin_prod` — the **sine-product form**:
  `∑_{n<2^m} ε(n)·e^(inx)
     = (-2i)^m·e^(i(2^m-1)x/2)·∏_{j<m} sin(2^j·x/2)`.
  At `x = -2πk/2^m` this is the atlas's closed dyadic DFT; taking
  `normSq` recovers the Riesz product, the phase having modulus one.
* `sum_thueMorseSign_mul_sin_affine` — the **affine sine-product form**,
  obtained by rotating the complex identity through an arbitrary phase
  and taking imaginary parts.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- **Half-angle factorization**: `1 - e^(iv) = -2i·e^(iv/2)·sin(v/2)`.
This is `one_sub_cexp_mul_I` at the real point `z = (v : ℂ)`. -/
theorem one_sub_exp_mul_I (v : ℝ) :
    1 - Complex.exp ((v : ℂ) * Complex.I) =
      -2 * Complex.I * Complex.exp (((v / 2 : ℝ) : ℂ) * Complex.I) *
        ((Real.sin (v / 2) : ℂ)) := by
  have hhalf : ((v / 2 : ℝ) : ℂ) = (v : ℂ) / 2 := by
    rw [Complex.ofReal_div, Complex.ofReal_ofNat]
  rw [Complex.ofReal_sin, hhalf]
  exact one_sub_cexp_mul_I (v : ℂ)

/-- **The sine-product form.**  On the unit circle,
`∑_{n<2^m} ε(n)·e^(inx)
   = (-2i)^m·e^(i(2^m-1)x/2)·∏_{j<m} sin(2^j·x/2)`.
This is `sum_thueMorseSign_cexp_eq_sin_prod` at the real point
`z = (x : ℂ)`. -/
theorem sum_thueMorseSign_exp_eq_sin_prod (x : ℝ) (m : ℕ) :
    ∑ n ∈ range (2 ^ m), ((thueMorseSign n : ℤ) : ℂ) *
        Complex.exp ((x : ℂ) * Complex.I) ^ n =
      (-2 * Complex.I) ^ m *
        Complex.exp ((((2 ^ m - 1 : ℕ) : ℝ) * x / 2 : ℝ) * Complex.I) *
        ∏ j ∈ range m, ((Real.sin (2 ^ j * x / 2) : ℂ)) := by
  have hphase : ((((2 ^ m - 1 : ℕ) : ℝ) * x / 2 : ℝ) : ℂ) =
      ((2 ^ m - 1 : ℕ) : ℂ) * (x : ℂ) / 2 := by
    rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast,
      Complex.ofReal_ofNat]
  have hsines : (∏ j ∈ range m, ((Real.sin (2 ^ j * x / 2) : ℂ))) =
      ∏ j ∈ range m, Complex.sin (((2 : ℂ) ^ j * (x : ℂ)) / 2) := by
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Complex.ofReal_sin, Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_ofNat]
  rw [hphase, hsines]
  exact sum_thueMorseSign_cexp_eq_sin_prod (x : ℂ) m

/-- **The affine sine-product form.** Rotating the complex Thue–Morse
polynomial through an arbitrary phase and taking imaginary parts gives
an exact real sine polynomial. -/
theorem sum_thueMorseSign_mul_sin_affine (x φ : ℝ) (m : ℕ) :
    ∑ n ∈ range (2 ^ m),
        (thueMorseSign n : ℝ) * Real.sin (φ + (n : ℝ) * x) =
      (2 : ℝ) ^ m * (∏ j ∈ range m, Real.sin (2 ^ j * x / 2)) *
        Real.sin
          (φ + ((2 ^ m - 1 : ℕ) : ℝ) * x / 2 -
            (m : ℝ) * Real.pi / 2) := by
  have hrotation :
      (-2 * Complex.I) ^ m =
        (2 : ℂ) ^ m *
          Complex.exp
            (((-(m : ℝ) * Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
    calc
      (-2 * Complex.I) ^ m =
          ((2 : ℂ) *
            Complex.exp (-((Real.pi : ℂ)) / 2 * Complex.I)) ^ m := by
        rw [Complex.exp_neg_pi_div_two_mul_I]
        apply congrArg (fun z : ℂ ↦ z ^ m)
        ring
      _ = (2 : ℂ) ^ m *
          Complex.exp (-((Real.pi : ℂ)) / 2 * Complex.I) ^ m := by
        rw [mul_pow]
      _ = (2 : ℂ) ^ m *
          Complex.exp
            (((-(m : ℝ) * Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
        rw [← Complex.exp_nat_mul]
        congr 2
        push_cast
        ring
  have hproduct :
      (∏ j ∈ range m, ((Real.sin (2 ^ j * x / 2) : ℂ))) =
        ((∏ j ∈ range m, Real.sin (2 ^ j * x / 2) : ℝ) : ℂ) := by
    push_cast
    rfl
  have hphase :
      Complex.exp ((φ : ℂ) * Complex.I) *
            Complex.exp
              (((-(m : ℝ) * Real.pi / 2 : ℝ) : ℂ) * Complex.I) *
            Complex.exp
              (((((2 ^ m - 1 : ℕ) : ℝ) * x / 2 : ℝ) : ℂ) * Complex.I) =
        Complex.exp
          (((φ + ((2 ^ m - 1 : ℕ) : ℝ) * x / 2 -
            (m : ℝ) * Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hexp_affine (n : ℕ) :
      Complex.exp
          ((((φ + (n : ℝ) * x : ℝ) : ℂ) * Complex.I)) =
        Complex.exp ((φ : ℂ) * Complex.I) *
          Complex.exp ((x : ℂ) * Complex.I) ^ n := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hcomplex :
      ∑ n ∈ range (2 ^ m), ((thueMorseSign n : ℤ) : ℂ) *
          Complex.exp
            ((((φ + (n : ℝ) * x : ℝ) : ℂ) * Complex.I)) =
        (((2 : ℝ) ^ m *
          ∏ j ∈ range m, Real.sin (2 ^ j * x / 2) : ℝ) : ℂ) *
          Complex.exp
            (((φ + ((2 ^ m - 1 : ℕ) : ℝ) * x / 2 -
              (m : ℝ) * Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
    calc
      ∑ n ∈ range (2 ^ m), ((thueMorseSign n : ℤ) : ℂ) *
          Complex.exp
            ((((φ + (n : ℝ) * x : ℝ) : ℂ) * Complex.I)) =
          Complex.exp ((φ : ℂ) * Complex.I) *
            ∑ n ∈ range (2 ^ m), ((thueMorseSign n : ℤ) : ℂ) *
              Complex.exp ((x : ℂ) * Complex.I) ^ n := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        rw [hexp_affine]
        ring
      _ = Complex.exp ((φ : ℂ) * Complex.I) *
          ((-2 * Complex.I) ^ m *
            Complex.exp
              (((((2 ^ m - 1 : ℕ) : ℝ) * x / 2 : ℝ) : ℂ) * Complex.I) *
            ∏ j ∈ range m, ((Real.sin (2 ^ j * x / 2) : ℂ))) := by
        rw [sum_thueMorseSign_exp_eq_sin_prod]
      _ = (((2 : ℝ) ^ m *
          ∏ j ∈ range m, Real.sin (2 ^ j * x / 2) : ℝ) : ℂ) *
          Complex.exp
            (((φ + ((2 ^ m - 1 : ℕ) : ℝ) * x / 2 -
              (m : ℝ) * Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
        rw [hrotation, hproduct]
        calc
          Complex.exp ((φ : ℂ) * Complex.I) *
              ((2 : ℂ) ^ m *
                Complex.exp
                  (((-(m : ℝ) * Real.pi / 2 : ℝ) : ℂ) * Complex.I) *
                Complex.exp
                  (((((2 ^ m - 1 : ℕ) : ℝ) * x / 2 : ℝ) : ℂ) * Complex.I) *
                ((∏ j ∈ range m, Real.sin (2 ^ j * x / 2) : ℝ) : ℂ)) =
            ((2 : ℂ) ^ m *
              ((∏ j ∈ range m, Real.sin (2 ^ j * x / 2) : ℝ) : ℂ)) *
              (Complex.exp ((φ : ℂ) * Complex.I) *
                Complex.exp
                  (((-(m : ℝ) * Real.pi / 2 : ℝ) : ℂ) * Complex.I) *
                Complex.exp
                  (((((2 ^ m - 1 : ℕ) : ℝ) * x / 2 : ℝ) : ℂ) * Complex.I)) := by
            ring
          _ = ((2 : ℂ) ^ m *
              ((∏ j ∈ range m, Real.sin (2 ^ j * x / 2) : ℝ) : ℂ)) *
              Complex.exp
                (((φ + ((2 ^ m - 1 : ℕ) : ℝ) * x / 2 -
                  (m : ℝ) * Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
            rw [hphase]
          _ = (((2 : ℝ) ^ m *
              ∏ j ∈ range m, Real.sin (2 ^ j * x / 2) : ℝ) : ℂ) *
              Complex.exp
                (((φ + ((2 ^ m - 1 : ℕ) : ℝ) * x / 2 -
                  (m : ℝ) * Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
            push_cast
            rfl
  have him_left :
      (∑ n ∈ range (2 ^ m), ((thueMorseSign n : ℤ) : ℂ) *
          Complex.exp
            ((((φ + (n : ℝ) * x : ℝ) : ℂ) * Complex.I))).im =
        ∑ n ∈ range (2 ^ m),
          (thueMorseSign n : ℝ) * Real.sin (φ + (n : ℝ) * x) := by
    rw [Complex.im_sum]
    apply Finset.sum_congr rfl
    intro n _
    simp only [Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
      Complex.exp_ofReal_mul_I_im, zero_mul, add_zero]
  have him_right :
      ((((2 : ℝ) ^ m *
          ∏ j ∈ range m, Real.sin (2 ^ j * x / 2) : ℝ) : ℂ) *
          Complex.exp
            (((φ + ((2 ^ m - 1 : ℕ) : ℝ) * x / 2 -
              (m : ℝ) * Real.pi / 2 : ℝ) : ℂ) * Complex.I)).im =
        (2 : ℝ) ^ m * (∏ j ∈ range m, Real.sin (2 ^ j * x / 2)) *
          Real.sin
            (φ + ((2 ^ m - 1 : ℕ) : ℝ) * x / 2 -
              (m : ℝ) * Real.pi / 2) := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_im, zero_mul, add_zero]
  rw [← him_left, ← him_right]
  exact congrArg Complex.im hcomplex

end Fabius
