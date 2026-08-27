import FabiusFunction.RenormalizationIdentity

/-!
# Centered sinc products and the Fourier--Laplace rotation

The research-frontier drafts use the centered product

`Q(z) = ∏' n, sinc (z / 2^(n+1))`.

This is exactly Rvachev's Fourier product after the normalization
`z ↦ z / (2π)`.  Making that change of coordinates explicit turns the
Fourier--Laplace ``Wick rotation'' into a theorem on the whole complex plane:

`exp (-z/2) * G(z) = Q(i z/2)`.

The module also records the finite products and their exact shell
factorization.  Thus the centered shell law has no separate exponential
prefactor: its tail is literally a smaller copy of the same centered entire
function.
-/

set_option autoImplicit false

open Filter
open scoped BigOperators Topology

namespace Fabius

noncomputable section

/-- The first `N` factors of the centered sinc product
`Q(z) = ∏_{k≥1} sinc(z/2^k)`. -/
noncomputable def centeredSincPartialProduct (z : ℂ) (N : ℕ) : ℂ :=
  ∏ n ∈ Finset.range N, complexSinc (z / (2 : ℂ) ^ (n + 1))

/-- The centered sinc product `Q(z) = ∏_{k≥1} sinc(z/2^k)` used in the
Fourier--Laplace rotation. -/
noncomputable def centeredSincProduct (z : ℂ) : ℂ :=
  ∏' n : ℕ, complexSinc (z / (2 : ℂ) ^ (n + 1))

private lemma normalized_fourier_argument (z : ℂ) (n : ℕ) :
    (Real.pi : ℂ) * (z / (2 * Real.pi)) / (2 : ℂ) ^ n =
      z / (2 : ℂ) ^ (n + 1) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  rw [pow_succ]
  field_simp [hpi]
  <;> ring

/-- The centered product is Rvachev's canonical Fourier product in the
frequency coordinate `z / (2π)`. -/
theorem centeredSincProduct_eq_rvachevFourierProduct (z : ℂ) :
    centeredSincProduct z =
      rvachevFourierProduct (z / (2 * Real.pi)) := by
  unfold centeredSincProduct rvachevFourierProduct
  apply tprod_congr
  intro n
  rw [normalized_fourier_argument]

/-- The same normalization for a finite prefix of the centered product. -/
theorem centeredSincPartialProduct_eq_fourierPrefix (z : ℂ) (N : ℕ) :
    centeredSincPartialProduct z N =
      ∏ n ∈ Finset.range N,
        complexSinc
          ((Real.pi : ℂ) * (z / (2 * Real.pi)) / (2 : ℂ) ^ n) := by
  unfold centeredSincPartialProduct
  apply Finset.prod_congr rfl
  intro n _hn
  rw [normalized_fourier_argument]

/-- The centered sinc factors form a genuinely convergent infinite product
at every complex argument. -/
theorem centeredSincFactors_multipliable (z : ℂ) :
    Multipliable (fun n : ℕ =>
      complexSinc (z / (2 : ℂ) ^ (n + 1))) := by
  have h := sincFactors_multipliable (z / (2 * Real.pi))
  convert h using 1
  funext n
  rw [normalized_fourier_argument]

/-- Finite centered products converge to the centered infinite product. -/
theorem tendsto_centeredSincPartialProduct (z : ℂ) :
    Tendsto (fun N : ℕ => centeredSincPartialProduct z N) atTop
      (nhds (centeredSincProduct z)) := by
  simpa [centeredSincPartialProduct, centeredSincProduct] using
    (centeredSincFactors_multipliable z).tendsto_prod_tprod_nat

/-- The centered sinc product is even. -/
theorem centeredSincProduct_neg (z : ℂ) :
    centeredSincProduct (-z) = centeredSincProduct z := by
  rw [centeredSincProduct_eq_rvachevFourierProduct,
    centeredSincProduct_eq_rvachevFourierProduct]
  have harg : (-z) / (2 * (Real.pi : ℂ)) =
      -(z / (2 * (Real.pi : ℂ))) := by ring
  rw [harg, rvachevFourierProduct_neg]

/-- Exact finite-shell factorization of the centered sinc product:
`Q(z) = Q_N(z) Q(z/2^N)`. -/
theorem centeredSincProduct_shell (z : ℂ) (N : ℕ) :
    centeredSincProduct z =
      centeredSincPartialProduct z N *
        centeredSincProduct (z / (2 : ℂ) ^ N) := by
  calc
    centeredSincProduct z =
        rvachevFourierProduct (z / (2 * Real.pi)) :=
      centeredSincProduct_eq_rvachevFourierProduct z
    _ = (∏ n ∈ Finset.range N,
          complexSinc
            ((Real.pi : ℂ) * (z / (2 * Real.pi)) / (2 : ℂ) ^ n)) *
        rvachevFourierProduct
          ((z / (2 * Real.pi)) / (2 : ℂ) ^ N) :=
      rvachevFourierProduct_shell N (z / (2 * Real.pi))
    _ = centeredSincPartialProduct z N *
        centeredSincProduct (z / (2 : ℂ) ^ N) := by
      rw [← centeredSincPartialProduct_eq_fourierPrefix,
        centeredSincProduct_eq_rvachevFourierProduct]
      congr 2
      ring

/-- The half-moment generating function is the centered sinc product after
the complex rotation `z ↦ i z/2`, with the displacement of the mean `1/2`
carried by the elementary exponential factor. -/
theorem complexGeneratingFunction_eq_exp_mul_centeredSincProduct
    (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) :
    complexGeneratingFunction F z =
      Complex.exp (z / 2) *
        centeredSincProduct (Complex.I * z / 2) := by
  rw [complexGeneratingFunction_eq_fourier_analytic F hF z,
    rvachevFourier_eq_product F hF,
    centeredSincProduct_eq_rvachevFourierProduct]
  congr 2
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  field_simp [hpi]
  <;> ring

/-- The Fourier--Laplace rotation in the negative-axis convention of the
research-frontier report: `G(-s) = exp(-s/2) Q(i s/2)`.  It holds for every
complex `s`, not merely on the positive real axis. -/
theorem complexGeneratingFunction_neg_eq_exp_mul_centeredSincProduct
    (F : BoundedFabius) (hF : IsFabius F) (s : ℂ) :
    complexGeneratingFunction F (-s) =
      Complex.exp (-s / 2) *
        centeredSincProduct (Complex.I * s / 2) := by
  calc
    complexGeneratingFunction F (-s) =
        Complex.exp ((-s) / 2) *
          centeredSincProduct (Complex.I * (-s) / 2) :=
      complexGeneratingFunction_eq_exp_mul_centeredSincProduct F hF (-s)
    _ = Complex.exp (-s / 2) *
        centeredSincProduct (-(Complex.I * s / 2)) := by
      congr 2 <;> ring
    _ = Complex.exp (-s / 2) *
        centeredSincProduct (Complex.I * s / 2) := by
      rw [centeredSincProduct_neg]

/-- The mean-centered entire generating function. -/
noncomputable def centeredComplexGeneratingFunction
    (F : BoundedFabius) (z : ℂ) : ℂ :=
  Complex.exp (-z / 2) * complexGeneratingFunction F z

/-- Whole-plane Wick rotation for the centered generating function:
`exp(-z/2) G(z) = Q(i z/2)`. -/
theorem centeredComplexGeneratingFunction_eq_centeredSincProduct
    (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) :
    centeredComplexGeneratingFunction F z =
      centeredSincProduct (Complex.I * z / 2) := by
  rw [centeredComplexGeneratingFunction,
    complexGeneratingFunction_eq_exp_mul_centeredSincProduct F hF]
  rw [← mul_assoc, ← Complex.exp_add]
  have hzero : -z / 2 + z / 2 = 0 := by ring
  rw [hzero, Complex.exp_zero, one_mul]

/-- The centered generating function is even, expressing reflection of the
Fabius law about its mean directly at the level of entire functions. -/
theorem centeredComplexGeneratingFunction_even
    (F : BoundedFabius) (hF : IsFabius F) :
    Function.Even (centeredComplexGeneratingFunction F) := by
  intro z
  rw [centeredComplexGeneratingFunction_eq_centeredSincProduct F hF,
    centeredComplexGeneratingFunction_eq_centeredSincProduct F hF]
  have harg : Complex.I * (-z) / 2 =
      -(Complex.I * z / 2) := by ring
  rw [harg, centeredSincProduct_neg]

/-- Exact centered tail law at every depth.  It simultaneously packages the
finite sinc product and the self-similar remainder:
`C(z) = Q_N(i z/2) C(z/2^N)`. -/
theorem centeredComplexGeneratingFunction_shell
    (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) (N : ℕ) :
    centeredComplexGeneratingFunction F z =
      centeredSincPartialProduct (Complex.I * z / 2) N *
        centeredComplexGeneratingFunction F (z / (2 : ℂ) ^ N) := by
  rw [centeredComplexGeneratingFunction_eq_centeredSincProduct F hF,
    centeredComplexGeneratingFunction_eq_centeredSincProduct F hF,
    centeredSincProduct_shell]
  congr 2
  ring

end

end Fabius
