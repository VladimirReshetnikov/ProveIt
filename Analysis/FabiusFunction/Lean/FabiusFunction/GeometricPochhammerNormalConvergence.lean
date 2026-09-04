import FabiusFunction.QPochhammerEntire
import FabiusFunction.EvenZetaSeries

/-!
# Normal convergence of the geometric q-Pochhammer factorization

The pointwise spectral factorization of `geometricSincProduct` is locally
uniform in the complex argument.  The outer spectral scales are summable,
while the entire q-Pochhammer factor differs from one to first order at the
origin.  Pulling the resulting scaled product back along `z ↦ z²` gives
the normal-convergence statement, including for the degenerate contraction
`q = 0`.

## Main results

* `hasProdLocallyUniformly_geometricSincProduct_complexQPochhammerInf`
  proves the general strict-contraction statement.
* `hasProdLocallyUniformly_rvachevFourierProduct_complexQPochhammerInf`
  specializes it to the dyadic Rvachev product and nome `1/4`.
* `hasProdLocallyUniformly_rvachevFourier_complexQPochhammerInf` transfers
  the dyadic statement to every bounded Fabius witness.
-/

set_option autoImplicit false

open Asymptotics Complex Filter Topology
open scoped BigOperators

namespace Fabius

noncomputable section

-- Match the analytic q-Pochhammer API's standard complex algebra hierarchy.
attribute [-instance] Complex.commRing

/-- The outer q-Pochhammer factorization of a geometric sinc product converges
locally uniformly on the whole complex plane.  No nonzero assumption on `q`
is needed, so the statement also covers the strict contraction `q = 0`. -/
theorem hasProdLocallyUniformly_geometricSincProduct_complexQPochhammerInf
    (q : ℂ) (hq : ‖q‖ < 1) :
    HasProdLocallyUniformly
      (fun (k : ℕ) (z : ℂ) =>
        complexQPochhammerInf
          (z ^ 2 / ((k : ℂ) + 1) ^ 2) (q ^ 2))
      (geometricSincProduct q) := by
  let f : ℂ → ℂ := fun w => complexQPochhammerInf w (q ^ 2)
  let a : ℕ → ℂ := fun k => 1 / ((k : ℂ) + 1) ^ 2
  have hq_sq : ‖q ^ 2‖ < 1 := by
    simpa only [norm_pow] using
      (pow_lt_one₀ (norm_nonneg q) hq two_ne_zero)
  have ha : Summable fun k : ℕ => ‖a k‖ := by
    refine (summable_one_div_add_one_pow (k := 1) one_ne_zero).congr
      fun k => ?_
    have hk : ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 := by
      rw [show ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) by push_cast; ring,
        Complex.norm_natCast]
      push_cast
      ring
    simp only [a, Nat.mul_one, norm_div, norm_one, norm_pow, hk]
  have hf : Differentiable ℂ f :=
    complexQPochhammerInf_differentiable (q ^ 2) hq_sq
  have hf0 : f 0 = 1 := by
    simp [f, complexQPochhammerInf, qPochhammerInfIn]
  have hfO : (fun w => f w - 1) =O[𝓝 0] (fun w : ℂ => w) := by
    simpa only [hf0, sub_self, sub_zero] using (hf 0).isBigO_sub
  have hprod :=
    hasProdLocallyUniformly_scaled f a ha hfO hf.continuous
  have hprod_sq :
      HasProdLocallyUniformly
        (fun (k : ℕ) (z : ℂ) => f (a k • z ^ 2))
        (fun z : ℂ => ∏' k : ℕ, f (a k • z ^ 2)) := by
    rw [hasProdLocallyUniformly_iff_tendstoLocallyUniformly] at hprod ⊢
    simpa only [Function.comp_def] using
      hprod.comp (fun z : ℂ => z ^ 2)
        (by fun_prop : Continuous fun z : ℂ => z ^ 2)
  have houter :
      HasProdLocallyUniformly
        (fun (k : ℕ) (z : ℂ) =>
          complexQPochhammerInf
            (z ^ 2 / ((k : ℂ) + 1) ^ 2) (q ^ 2))
        (fun z : ℂ => ∏' k : ℕ,
          complexQPochhammerInf
            (z ^ 2 / ((k : ℂ) + 1) ^ 2) (q ^ 2)) := by
    simpa only [f, a, smul_eq_mul, one_div, div_eq_mul_inv, mul_comm, one_mul]
      using hprod_sq
  have hlimit :
      (fun z : ℂ => ∏' k : ℕ,
        complexQPochhammerInf
          (z ^ 2 / ((k : ℂ) + 1) ^ 2) (q ^ 2)) =
        geometricSincProduct q := by
    funext z
    exact
      (geometricSincProduct_eq_tprod_complexQPochhammerInf q z hq).symm
  rw [hlimit] at houter
  exact houter

/-- The dyadic outer q-Pochhammer product with nome `1/4` converges locally
uniformly to the standalone Rvachev Fourier product. -/
theorem hasProdLocallyUniformly_rvachevFourierProduct_complexQPochhammerInf :
    HasProdLocallyUniformly
      (fun (k : ℕ) (z : ℂ) =>
        complexQPochhammerInf
          (z ^ 2 / ((k : ℂ) + 1) ^ 2) (1 / 4 : ℂ))
      rvachevFourierProduct := by
  have h :=
    hasProdLocallyUniformly_geometricSincProduct_complexQPochhammerInf
      ((2 : ℂ)⁻¹) (by norm_num)
  have hlimit :
      geometricSincProduct ((2 : ℂ)⁻¹) = rvachevFourierProduct := by
    funext z
    exact geometricSincProduct_inv_two z
  rw [hlimit] at h
  simpa only [show (((2 : ℂ)⁻¹) ^ 2) = (1 / 4 : ℂ) by norm_num]
    using h

/-- For every bounded Fabius witness, the dyadic outer q-Pochhammer product
converges locally uniformly to its Fourier transform. -/
theorem hasProdLocallyUniformly_rvachevFourier_complexQPochhammerInf
    (F : BoundedFabius) (hF : IsFabius F) :
    HasProdLocallyUniformly
      (fun (k : ℕ) (z : ℂ) =>
        complexQPochhammerInf
          (z ^ 2 / ((k : ℂ) + 1) ^ 2) (1 / 4 : ℂ))
      (rvachevFourier F) := by
  have h :=
    hasProdLocallyUniformly_rvachevFourierProduct_complexQPochhammerInf
  have hlimit : rvachevFourier F = rvachevFourierProduct := by
    funext z
    exact rvachevFourier_eq_product F hF z
  rw [← hlimit] at h
  exact h

end

end Fabius
