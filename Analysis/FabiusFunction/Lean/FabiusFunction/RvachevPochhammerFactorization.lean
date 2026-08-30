import FabiusFunction.SincCanonicalProduct
import FabiusFunction.FiniteQBinomialCore

/-!
# Complex q-Pochhammer factorization of the Rvachev product

This module packages the complex infinite q-Pochhammer symbol and identifies
the dyadic Rvachev sinc product with a product of quarter-base q-Pochhammer
symbols.  Absolute summability of the already established double Euler
product justifies the exchange of the scale and zero indices, so the final
factorization is global in the complex argument and requires no nonvanishing
condition.

## Main results

* `complexQPochhammerInf` is the complex infinite q-Pochhammer product.
* `multipliable_one_sub_mul_pow_complex`,
  `hasProd_complexQPochhammerInf`, and
  `tendsto_finiteQPochhammerIn_complex` give its convergence for `‖q‖ < 1`.
* `rvachevFourierProduct_eq_tprod_complexQPochhammerInf` rewrites the
  standalone Rvachev sinc product as a product of nome-`1/4` symbols.
* `rvachevFourier_eq_tprod_complexQPochhammerInf` transfers the same
  factorization to the Fourier transform of every bounded Fabius witness.
-/

set_option autoImplicit false

open Complex Filter Topology
open scoped BigOperators

namespace Fabius

noncomputable section

-- Avoid the computable shortcut instance here: the imported analytic product
-- theorems use the standard noncomputable complex field/C⋆-algebra hierarchy.
attribute [-instance] Complex.commRing

/-- The complex infinite q-Pochhammer symbol `(a;q)_∞`. -/
noncomputable def complexQPochhammerInf (a q : ℂ) : ℂ :=
  ∏' j : ℕ, (1 - a * q ^ j)

/-- The defining infinite-product presentation of `complexQPochhammerInf`. -/
theorem complexQPochhammerInf_eq_tprod (a q : ℂ) :
    complexQPochhammerInf a q =
      ∏' j : ℕ, (1 - a * q ^ j) := rfl

/-- The complex q-Pochhammer factor family is multipliable whenever the nome
has norm strictly below one. -/
theorem multipliable_one_sub_mul_pow_complex
    (a : ℂ) {q : ℂ} (hq : ‖q‖ < 1) :
    Multipliable fun j : ℕ => 1 - a * q ^ j := by
  have hsum : Summable fun j : ℕ => -a * q ^ j :=
    (summable_geometric_of_norm_lt_one hq).mul_left (-a)
  exact (multipliable_one_add_of_summable hsum.norm).congr fun j => by
    ring

/-- The complex q-Pochhammer factors have product
`complexQPochhammerInf a q` for every contracting nome. -/
theorem hasProd_complexQPochhammerInf
    (a : ℂ) {q : ℂ} (hq : ‖q‖ < 1) :
    HasProd (fun j : ℕ => 1 - a * q ^ j)
      (complexQPochhammerInf a q) := by
  simpa only [complexQPochhammerInf] using
    (multipliable_one_sub_mul_pow_complex a hq).hasProd

/-- Finite complex q-Pochhammer products converge to the infinite symbol for
every contracting nome. -/
theorem tendsto_finiteQPochhammerIn_complex
    (a : ℂ) {q : ℂ} (hq : ‖q‖ < 1) :
    Tendsto (fun n : ℕ => finiteQPochhammerIn a q n) atTop
      (𝓝 (complexQPochhammerInf a q)) := by
  simpa only [finiteQPochhammerIn, complexQPochhammerInf] using
    (multipliable_one_sub_mul_pow_complex a hq).tendsto_prod_tprod_nat

private theorem one_add_sineTerm_div_two_pow_eq_pochhammerFactor
    (z : ℂ) (h k : ℕ) :
    1 + sineTerm (z / (2 : ℂ) ^ h) k =
      1 - (z ^ 2 / ((k : ℂ) + 1) ^ 2) * (1 / 4 : ℂ) ^ h := by
  have hpow4 : (((2 : ℂ) ^ h) ^ 2) = (4 : ℂ) ^ h := by
    rw [← pow_mul, mul_comm h 2, pow_mul]
    norm_num
  simp only [sineTerm, div_pow, one_pow, hpow4]
  ring

/-- **Spectral q-Pochhammer factorization of the Rvachev product.**  For
every complex `z`,

`rvachevFourierProduct z = ∏' k, (z²/(k+1)²; 1/4)_∞`.

The theorem is global: absolute summability of the double sine-product
perturbation permits the index exchange, including at zeros of individual
factors. -/
theorem rvachevFourierProduct_eq_tprod_complexQPochhammerInf (z : ℂ) :
    rvachevFourierProduct z =
      ∏' k : ℕ,
        complexQPochhammerInf
          (z ^ 2 / ((k : ℂ) + 1) ^ 2) (1 / 4 : ℂ) := by
  let f : ℕ → ℕ → ℂ := fun h k =>
    1 + sineTerm (z / 2 ^ h) k
  have hf : Multipliable (Function.uncurry f) := by
    change Multipliable fun p : ℕ × ℕ =>
      1 + sineTerm (z / 2 ^ p.1) p.2
    exact multipliable_one_add_of_summable
      (summable_norm_sineTerm_pair z)
  have hquarter : ‖(1 / 4 : ℂ)‖ < 1 := by
    norm_num
  have hf_col : ∀ k : ℕ, Multipliable fun h : ℕ => f h k := by
    intro k
    refine (multipliable_one_sub_mul_pow_complex
      (z ^ 2 / ((k : ℂ) + 1) ^ 2) hquarter).congr ?_
    intro h
    exact (one_add_sineTerm_div_two_pow_eq_pochhammerFactor z h k).symm
  calc
    rvachevFourierProduct z =
        ∏' p : ℕ × ℕ, Function.uncurry f p := by
      change rvachevFourierProduct z =
        ∏' p : ℕ × ℕ,
          (1 + sineTerm (z / 2 ^ p.1) p.2)
      exact rvachevFourierProduct_eq_tprod_pair z
    _ = ∏' p : ℕ × ℕ, Function.uncurry f p.swap := by
      simpa only [Equiv.prodComm_apply] using
        ((Equiv.prodComm ℕ ℕ).tprod_eq (Function.uncurry f)).symm
    _ = ∏' k : ℕ, ∏' h : ℕ, f h k := by
      exact hf.prod_symm.tprod_prod' hf_col
    _ = ∏' k : ℕ,
        complexQPochhammerInf
          (z ^ 2 / ((k : ℂ) + 1) ^ 2) (1 / 4 : ℂ) := by
      refine tprod_congr fun k => ?_
      rw [complexQPochhammerInf_eq_tprod]
      refine tprod_congr fun h => ?_
      simpa only [f] using
        one_add_sineTerm_div_two_pow_eq_pochhammerFactor z h k

/-- The spectral q-Pochhammer factorization for the Fourier transform of
every bounded Fabius witness. -/
theorem rvachevFourier_eq_tprod_complexQPochhammerInf
    (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) :
    rvachevFourier F z =
      ∏' k : ℕ,
        complexQPochhammerInf
          (z ^ 2 / ((k : ℂ) + 1) ^ 2) (1 / 4 : ℂ) := by
  rw [rvachevFourier_eq_product F hF,
    rvachevFourierProduct_eq_tprod_complexQPochhammerInf]

end

end Fabius
