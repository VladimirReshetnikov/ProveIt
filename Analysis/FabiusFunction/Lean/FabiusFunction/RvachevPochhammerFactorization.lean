import FabiusFunction.SincCanonicalProduct
import FabiusFunction.FiniteQBinomialCore
import FabiusFunction.GeometricReciprocalGamma
import FabiusFunction.QPochhammerInfinite

/-!
# Complex q-Pochhammer factorization of geometric sinc products

This module packages the complex infinite q-Pochhammer symbol and identifies
every geometric sinc product with a spectral product of q-Pochhammer symbols.
The main theorem works for an arbitrary strict complex contraction; the
Rvachev identity is its dyadic specialization.  Absolute summability of the
double Euler product justifies the exchange of scale and zero indices, so the
factorization is global in the complex argument and requires no nonvanishing
condition.

## Main results

* `complexQPochhammerInf` is the complex infinite q-Pochhammer product.
* `complexQPochhammerInf_eq_qPochhammerInfIn` identifies it with the generic
  topological-ring symbol.
* `multipliable_one_sub_mul_pow_complex`,
  `hasProd_complexQPochhammerInf`, and
  `tendsto_finiteQPochhammerIn_complex` give its convergence for `‖q‖ < 1`.
* `geometricSincProduct_eq_tprod_complexQPochhammerInf` generalizes that
  factorization to every strict complex contraction and nome `q ^ 2`.
* `rvachevFourierProduct_eq_tprod_complexQPochhammerInf` is the dyadic
  nome-`1/4` specialization for the standalone Rvachev sinc product.
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

/-- The historical complex q-Pochhammer name is exactly the specialization of
the generic infinite q-Pochhammer symbol to the complex numbers. -/
theorem complexQPochhammerInf_eq_qPochhammerInfIn (a q : ℂ) :
    complexQPochhammerInf a q = qPochhammerInfIn a q := rfl

/-- The complex q-Pochhammer factor family is multipliable whenever the nome
has norm strictly below one. -/
theorem multipliable_one_sub_mul_pow_complex
    (a : ℂ) {q : ℂ} (hq : ‖q‖ < 1) :
    Multipliable fun j : ℕ => 1 - a * q ^ j :=
  multipliable_one_sub_mul_pow_of_norm_lt_one a hq

/-- The complex q-Pochhammer factors have product
`complexQPochhammerInf a q` for every contracting nome. -/
theorem hasProd_complexQPochhammerInf
    (a : ℂ) {q : ℂ} (hq : ‖q‖ < 1) :
    HasProd (fun j : ℕ => 1 - a * q ^ j)
      (complexQPochhammerInf a q) := by
  rw [complexQPochhammerInf_eq_qPochhammerInfIn]
  exact hasProd_qPochhammerInfIn a hq

/-- Finite complex q-Pochhammer products converge to the infinite symbol for
every contracting nome. -/
theorem tendsto_finiteQPochhammerIn_complex
    (a : ℂ) {q : ℂ} (hq : ‖q‖ < 1) :
    Tendsto (fun n : ℕ => finiteQPochhammerIn a q n) atTop
      (𝓝 (complexQPochhammerInf a q)) := by
  rw [complexQPochhammerInf_eq_qPochhammerInfIn]
  exact tendsto_finiteQPochhammerIn_qPochhammerInfIn a hq

/-- The double Euler perturbation for a geometric sinc product is absolutely
summable whenever the scale is a strict complex contraction. -/
theorem summable_norm_sineTerm_qpow_pair
    {q : ℂ} (hq : ‖q‖ < 1) (z : ℂ) :
    Summable fun p : ℕ × ℕ => ‖sineTerm (q ^ p.1 * z) p.2‖ := by
  have hq_sq : ‖q‖ ^ 2 < 1 := by
    exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have hgeo : Summable fun h : ℕ => ‖z‖ ^ 2 * (‖q‖ ^ 2) ^ h :=
    (summable_geometric_of_lt_one (sq_nonneg _) hq_sq).mul_left _
  have hp2 : Summable fun k : ℕ => ((1 : ℝ) / ((k + 1) ^ 2)) := by
    have h := Real.summable_one_div_nat_pow.mpr one_lt_two
    exact_mod_cast (summable_nat_add_iff 1).mpr h
  have hsum := hgeo.mul_of_nonneg hp2
    (fun h => by positivity) (fun k => by positivity)
  refine hsum.congr fun p => ?_
  obtain ⟨h, k⟩ := p
  have hnk : ‖(k : ℂ) + 1‖ = (k : ℝ) + 1 := by
    have hc := Complex.norm_natCast (k + 1)
    push_cast at hc
    exact hc
  have hpow : ((‖q‖ ^ h) ^ 2) = (‖q‖ ^ 2) ^ h := by
    rw [← pow_mul, mul_comm h 2, pow_mul]
  simp only [sineTerm, norm_div, norm_neg, norm_pow, norm_mul]
  rw [hnk, mul_pow, hpow]
  ring

/-- A geometric sinc product is the product of its scale-by-spectral-zero
Euler factors.  Absolute multipliability justifies the paired indexing. -/
theorem geometricSincProduct_eq_tprod_pair
    {q : ℂ} (hq : ‖q‖ < 1) (z : ℂ) :
    geometricSincProduct q z =
      ∏' p : ℕ × ℕ, (1 + sineTerm (q ^ p.1 * z) p.2) := by
  have hmult : Multipliable fun p : ℕ × ℕ =>
      1 + sineTerm (q ^ p.1 * z) p.2 :=
    multipliable_one_add_of_summable
      (summable_norm_sineTerm_qpow_pair hq z)
  have hrow : ∀ h : ℕ, Multipliable fun k : ℕ =>
      1 + sineTerm (q ^ h * z) k := fun h =>
    multipliable_sineTerm (q ^ h * z)
  calc
    geometricSincProduct q z =
        ∏' h : ℕ, complexSinc ((Real.pi : ℂ) * (q ^ h * z)) := rfl
    _ = ∏' h : ℕ, ∏' k : ℕ,
        (1 + sineTerm (q ^ h * z) k) := by
      refine tprod_congr fun h => ?_
      rw [← tprod_one_add_sineTerm (q ^ h * z)]
    _ = ∏' p : ℕ × ℕ,
        (1 + sineTerm (q ^ p.1 * z) p.2) :=
      (hmult.tprod_prod' hrow).symm

private theorem one_add_sineTerm_qpow_eq_pochhammerFactor
    (q z : ℂ) (h k : ℕ) :
    1 + sineTerm (q ^ h * z) k =
      1 - (z ^ 2 / ((k : ℂ) + 1) ^ 2) * (q ^ 2) ^ h := by
  have hpow : ((q ^ h) ^ 2) = (q ^ 2) ^ h := by
    rw [← pow_mul, mul_comm h 2, pow_mul]
  rw [sineTerm, mul_pow, hpow]
  ring

/-- **Global spectral q-Pochhammer factorization of the geometric sinc
product.**  For every strict complex contraction `q` and every `z : ℂ`,

`geometricSincProduct q z = ∏' k, (z²/(k+1)²; q²)_∞`.

Absolute summability of the double Euler-factor family permits the exchange
of the geometric-scale and spectral-zero indices.  The statement includes
the degenerate contraction `q = 0` and remains valid at every zero of an
individual factor. -/
theorem geometricSincProduct_eq_tprod_complexQPochhammerInf
    (q z : ℂ) (hq : ‖q‖ < 1) :
    geometricSincProduct q z =
      ∏' k : ℕ,
        complexQPochhammerInf
          (z ^ 2 / ((k : ℂ) + 1) ^ 2) (q ^ 2) := by
  let f : ℕ → ℕ → ℂ := fun h k =>
    1 + sineTerm (q ^ h * z) k
  have hf : Multipliable (Function.uncurry f) := by
    change Multipliable fun p : ℕ × ℕ =>
      1 + sineTerm (q ^ p.1 * z) p.2
    exact multipliable_one_add_of_summable
      (summable_norm_sineTerm_qpow_pair hq z)
  have hq_sq : ‖q ^ 2‖ < 1 := by
    simpa only [norm_pow] using
      (pow_lt_one₀ (norm_nonneg q) hq two_ne_zero)
  have hf_col : ∀ k : ℕ, Multipliable fun h : ℕ => f h k := by
    intro k
    refine (multipliable_one_sub_mul_pow_complex
      (z ^ 2 / ((k : ℂ) + 1) ^ 2) hq_sq).congr ?_
    intro h
    exact (one_add_sineTerm_qpow_eq_pochhammerFactor q z h k).symm
  calc
    geometricSincProduct q z =
        ∏' p : ℕ × ℕ, Function.uncurry f p := by
      change geometricSincProduct q z =
        ∏' p : ℕ × ℕ, (1 + sineTerm (q ^ p.1 * z) p.2)
      exact geometricSincProduct_eq_tprod_pair hq z
    _ = ∏' p : ℕ × ℕ, Function.uncurry f p.swap := by
      simpa only [Equiv.prodComm_apply] using
        ((Equiv.prodComm ℕ ℕ).tprod_eq (Function.uncurry f)).symm
    _ = ∏' k : ℕ, ∏' h : ℕ, f h k := by
      exact hf.prod_symm.tprod_prod' hf_col
    _ = ∏' k : ℕ,
        complexQPochhammerInf
          (z ^ 2 / ((k : ℂ) + 1) ^ 2) (q ^ 2) := by
      refine tprod_congr fun k => ?_
      rw [complexQPochhammerInf_eq_tprod]
      refine tprod_congr fun h => ?_
      simpa only [f] using
        one_add_sineTerm_qpow_eq_pochhammerFactor q z h k

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
  calc
    rvachevFourierProduct z =
        geometricSincProduct ((2 : ℂ)⁻¹) z :=
      (geometricSincProduct_inv_two z).symm
    _ = ∏' k : ℕ,
        complexQPochhammerInf
          (z ^ 2 / ((k : ℂ) + 1) ^ 2) (((2 : ℂ)⁻¹) ^ 2) :=
      geometricSincProduct_eq_tprod_complexQPochhammerInf
        ((2 : ℂ)⁻¹) z (by norm_num)
    _ = ∏' k : ℕ,
        complexQPochhammerInf
          (z ^ 2 / ((k : ℂ) + 1) ^ 2) (1 / 4 : ℂ) := by
      norm_num

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
