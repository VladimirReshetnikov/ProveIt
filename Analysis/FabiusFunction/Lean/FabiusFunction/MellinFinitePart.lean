import FabiusFunction.MellinBose

/-!
# The finite part of the Gamma--zeta Mellin product

This file regularizes the product `Γ(s) ζ(1+s)` at `s = 0`.  The poles of
the two factors combine to a double pole.  After subtracting that pole, the
finite part is the Euler--Stieltjes combination `gammaZetaConstant` defined in
`FabiusFunction.StieltjesConstant`.

The final real right-hand limit is the form consumed by the mean computation
for the negative-Laplace periodic correction.
-/

set_option autoImplicit false

open scoped BigOperators Topology Interval
open Set Filter MeasureTheory Asymptotics

namespace Fabius

/-- The product in which both singular factors have been regularized by one
factor of `s`. -/
noncomputable def gammaZetaRegularProduct (s : ℂ) : ℂ :=
  Complex.Gamma (1 + s) * (s * riemannZeta (1 + s))

/-- Away from the origin, the regular product is the singular Gamma--zeta
product multiplied by the two powers of `s` that cancel its double pole. -/
lemma gammaZetaRegularProduct_eq_sq_mul (s : ℂ) (hs : s ≠ 0) :
    gammaZetaRegularProduct s =
      s ^ 2 * Complex.Gamma s * riemannZeta (1 + s) := by
  unfold gammaZetaRegularProduct
  rw [show 1 + s = s + 1 by ring, Complex.Gamma_add_one s hs]
  ring

/-- The second-order Taylor expansion of the regular Gamma--zeta product.

Its quadratic coefficient is the negative of `gammaZetaConstant`. -/
lemma gammaZetaRegularProduct_taylor_second :
    (fun s : ℂ => gammaZetaRegularProduct s -
      (1 - (gammaZetaConstant : ℂ) * s ^ 2)) =o[𝓝[≠] 0]
        (fun s : ℂ => s ^ 2) := by
  let γ : ℂ := Real.eulerMascheroniConstant
  let γ₁ : ℂ := firstStieltjesConstant
  let A : ℂ := γ ^ 2 / 2 + (Real.pi : ℂ) ^ 2 / 12
  let C : ℂ := gammaZetaConstant
  let G : ℂ → ℂ := fun s => Complex.Gamma (1 + s)
  let Z : ℂ → ℂ := fun s => s * riemannZeta (1 + s)
  let P : ℂ → ℂ := fun s => 1 - γ * s + A * s ^ 2
  let Q : ℂ → ℂ := fun s => 1 + γ * s - γ₁ * s ^ 2
  let l : Filter ℂ := 𝓝[≠] 0
  have hG : (fun s => G s - P s) =o[l] (fun s : ℂ => s ^ 2) := by
    simpa only [G, P, γ, A, l] using
      complexGamma_one_add_taylor_second.mono nhdsWithin_le_nhds
  have hZ : (fun s => Z s - Q s) =o[l] (fun s : ℂ => s ^ 2) := by
    simpa only [Z, Q, γ, γ₁, l] using mul_riemannZeta_one_add_taylor_second
  have hs2O : (fun s : ℂ => s ^ 2) =O[l] (fun _ : ℂ => (1 : ℂ)) := by
    exact ((by fun_prop : ContinuousAt (fun s : ℂ => s ^ 2) 0).isBigO).mono
      nhdsWithin_le_nhds
  have hPO : P =O[l] (fun _ : ℂ => (1 : ℂ)) := by
    exact ((by fun_prop : ContinuousAt P 0).isBigO).mono nhdsWithin_le_nhds
  have hQO : Q =O[l] (fun _ : ℂ => (1 : ℂ)) := by
    exact ((by fun_prop : ContinuousAt Q 0).isBigO).mono nhdsWithin_le_nhds
  have hZO : Z =O[l] (fun _ : ℂ => (1 : ℂ)) := by
    have herr : (fun s => Z s - Q s) =O[l] (fun _ : ℂ => (1 : ℂ)) :=
      hZ.isBigO.trans hs2O
    have hadd := herr.add hQO
    refine hadd.congr' (Filter.Eventually.of_forall fun s => ?_)
      (Filter.Eventually.of_forall fun _ => rfl)
    ring
  have hprod : (fun s => G s * Z s - P s * Q s) =o[l]
      (fun s : ℂ => s ^ 2) := by
    have h1raw := hG.mul_isBigO hZO
    have h1 : (fun s => (G s - P s) * Z s) =o[l]
        (fun s : ℂ => s ^ 2) := by
      exact h1raw.congr (fun s => rfl) (fun s => by simp)
    have h2raw := hPO.mul_isLittleO hZ
    have h2 : (fun s => P s * (Z s - Q s)) =o[l]
        (fun s : ℂ => s ^ 2) := by
      exact h2raw.congr (fun s => rfl) (fun s => by simp)
    have hadd := h1.add h2
    exact hadd.congr (fun s => by ring) (fun _ => rfl)
  have hpoly : (fun s => P s * Q s - (1 - C * s ^ 2)) =o[l]
      (fun s : ℂ => s ^ 2) := by
    have h3 : (fun s : ℂ => s ^ 3) =o[l] (fun s : ℂ => s ^ 2) :=
      (isLittleO_pow_pow (by norm_num : 2 < 3)).mono nhdsWithin_le_nhds
    have h4 : (fun s : ℂ => s ^ 4) =o[l] (fun s : ℂ => s ^ 2) :=
      (isLittleO_pow_pow (by norm_num : 2 < 4)).mono nhdsWithin_le_nhds
    let B : ℂ := γ * (γ₁ + A)
    let D : ℂ := -A * γ₁
    have hsum := (h3.const_mul_left B).add (h4.const_mul_left D)
    refine hsum.congr (fun s => ?_) (fun _ => rfl)
    dsimp [P, Q, C, B, D, A, γ, γ₁]
    unfold gammaZetaConstant
    push_cast
    ring
  have hsum := hprod.add hpoly
  refine hsum.congr (fun s => ?_) (fun _ => rfl)
  dsimp [gammaZetaRegularProduct, G, Z, P, Q, C]
  ring

/-- Dividing the regular product's quadratic defect by `s²` recovers its
finite part at the punctured origin. -/
theorem tendsto_gammaZetaRegularProduct_finitePart :
    Tendsto (fun s : ℂ => (1 - gammaZetaRegularProduct s) / s ^ 2)
      (𝓝[≠] 0) (𝓝 (gammaZetaConstant : ℂ)) := by
  have hzero := gammaZetaRegularProduct_taylor_second.tendsto_div_nhds_zero
  have hlim := (tendsto_const_nhds (x := (gammaZetaConstant : ℂ))).sub hzero
  have heq : (fun s : ℂ => (gammaZetaConstant : ℂ) -
      (gammaZetaRegularProduct s -
        (1 - (gammaZetaConstant : ℂ) * s ^ 2)) / s ^ 2) =ᶠ[𝓝[≠] 0]
      (fun s : ℂ => (1 - gammaZetaRegularProduct s) / s ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : s ≠ 0 := by simpa using hs
    field_simp [hs0]
    ring
  simpa using hlim.congr' heq

/-- Complex finite-part form of the singular Gamma--zeta product. -/
theorem tendsto_complexGamma_mul_zeta_finitePart :
    Tendsto (fun s : ℂ =>
      -Complex.Gamma s * riemannZeta (1 + s) + 1 / s ^ 2)
      (𝓝[≠] 0) (𝓝 (gammaZetaConstant : ℂ)) := by
  apply tendsto_gammaZetaRegularProduct_finitePart.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : s ≠ 0 := by simpa using hs
  rw [gammaZetaRegularProduct_eq_sq_mul s hs0]
  field_simp [hs0]
  ring

/-- Positive real numbers approach the origin inside the punctured complex
neighborhood under the canonical embedding. -/
lemma tendsto_ofReal_nhdsGT_punctured :
    Tendsto (fun a : ℝ => (a : ℂ)) (𝓝[>] 0) (𝓝[≠] 0) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · exact (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with a ha
    simpa using (ne_of_gt ha)

/-- Real right-hand finite-part limit used by the logarithmic Bose integral. -/
theorem tendsto_realGamma_mul_zeta_finitePart :
    Tendsto (fun a : ℝ =>
      -Real.Gamma a * (riemannZeta ((1 + a : ℝ) : ℂ)).re + 1 / a ^ 2)
      (𝓝[>] 0) (𝓝 gammaZetaConstant) := by
  have hc := tendsto_complexGamma_mul_zeta_finitePart.comp
    tendsto_ofReal_nhdsGT_punctured
  have hr := (Complex.continuous_re.tendsto
    (gammaZetaConstant : ℂ)).comp hc
  apply hr.congr'
  filter_upwards with a
  simp only [Function.comp_apply]
  rw [Complex.Gamma_ofReal]
  have hdiv : (1 / (a : ℂ) ^ 2) = ((1 / a ^ 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hdiv]
  rw [show (1 : ℂ) + (a : ℂ) = ((1 + a : ℝ) : ℂ) by push_cast; rfl]
  simp only [Complex.add_re, Complex.neg_re, Complex.neg_im, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, neg_zero, zero_mul, sub_zero]

end Fabius
