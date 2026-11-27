import GRHArticle.SingularModuli.ReducedForms
import Mathlib.Algebra.Polynomial.Eval.Subring

/-!
# Complex conjugation of the analytic class polynomial

Reflection of a reduced form either changes the sign of its middle coefficient
or returns the same representative on the boundary of the fundamental domain.
This proves real descent directly for the analytic product.
-/

namespace GRHArticle.SingularModuli

open Polynomial UpperHalfPlane
open scoped ComplexConjugate MatrixGroups

/-- The analytic invariant respects reflection across the imaginary axis. -/
theorem modularInvariant_J (z : ℍ) : modularInvariant (J • z) = conj (modularInvariant z) := by
  have hq : Function.Periodic.qParam 1 (↑(J • z : ℍ) : ℂ) = conj (Function.Periodic.qParam 1 z) := by
    rw [Function.Periodic.qParam, Function.Periodic.qParam, coe_J_smul, ← Complex.exp_conj]
    congr 1
    simp only [Complex.ofReal_one, div_one, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
    ring
  have ht (f : ℕ → ℂ) : conj (∏' n, f n) = ∏' n, conj (f n) :=
    Function.LeftInverse.map_tprod (g := starRingEnd ℂ) f Complex.continuous_conj
      Complex.continuous_conj star_star
  rw [modularInvariant_qExpansion (J • z), modularInvariant_qExpansion z, hq]
  simp only [map_div₀, map_pow, map_mul, map_add, map_sub, map_one, map_ofNat, map_natCast,
    Complex.conj_tsum, ht]

private theorem J_quadraticPoint (D a : ℕ+) (b : ℤ) :
    J • quadraticPoint D a b = quadraticPoint D a (-b) := by
  rw [UpperHalfPlane.ext_iff, coe_J_smul]
  apply Complex.ext <;> simp [quadraticPoint, neg_div]

private theorem J_quadraticPoint_eq_T (D a : ℕ+) (b : ℤ) (hb : b = (a : ℤ)) :
    J • quadraticPoint D a b = ModularGroup.T • quadraticPoint D a b := by
  rw [UpperHalfPlane.ext_iff, coe_J_smul, modular_T_smul, coe_vadd]
  have hbr : (b : ℝ) = (a : ℝ) := by exact_mod_cast hb
  apply Complex.ext
  · simp only [Complex.neg_re, Complex.conj_re, quadraticPoint, coe_mk, Complex.add_re,
      Complex.ofReal_re, hbr]
    field_simp [show (a : ℝ) ≠ 0 by positivity]
    norm_num
  · simp [quadraticPoint]

private theorem normSq_quadraticPoint (D a : ℕ+) (b c : ℤ)
    (hdisc : b ^ 2 - 4 * (a : ℤ) * c = -(D : ℤ)) :
    Complex.normSq (quadraticPoint D a b : ℂ) = (c : ℝ) / (a : ℝ) := by
  have hD : (0 : ℝ) ≤ D := by positivity
  have hdisc' : (b : ℝ) ^ 2 - 4 * (a : ℝ) * (c : ℝ) = -(D : ℝ) := by exact_mod_cast hdisc
  have hnum : (b : ℝ) ^ 2 + (D : ℝ) = 4 * (a : ℝ) * (c : ℝ) := by linarith only [hdisc']
  rw [Complex.normSq_apply]
  change (-(b : ℝ) / (2 * (a : ℝ))) * (-(b : ℝ) / (2 * (a : ℝ))) +
    (Real.sqrt (D : ℝ) / (2 * (a : ℝ))) * (Real.sqrt (D : ℝ) / (2 * (a : ℝ))) = _
  rw [← sq, ← sq, div_pow, div_pow, neg_sq, Real.sq_sqrt hD, ← add_div, hnum]
  field_simp [show (a : ℝ) ≠ 0 by positivity]
  ring

private theorem J_quadraticPoint_eq_S (D a : ℕ+) (b c : ℤ)
    (hdisc : b ^ 2 - 4 * (a : ℤ) * c = -(D : ℤ)) (hc : (a : ℤ) = c) :
    J • quadraticPoint D a b = ModularGroup.S • quadraticPoint D a b := by
  have hcr : (a : ℝ) = (c : ℝ) := by exact_mod_cast hc
  have hnorm := normSq_quadraticPoint D a b c hdisc
  rw [← hcr, div_self (show (a : ℝ) ≠ 0 by positivity)] at hnorm
  rw [UpperHalfPlane.ext_iff, coe_J_smul, modular_S_smul]
  change -conj (quadraticPoint D a b : ℂ) = (-(quadraticPoint D a b : ℂ))⁻¹
  rw [inv_neg, Complex.inv_def, hnorm]
  simp

/-- Reflection of a reduced representative, with the boundary sign convention. -/
def reflectReducedForm (f : FormCoefficients) : FormCoefficients :=
  if |f.b| = (f.a : ℤ) ∨ (f.a : ℤ) = f.c then f else ⟨f.a, -f.b, f.c⟩

theorem reflectReducedForm_involutive : Function.Involutive reflectReducedForm := by
  intro f
  by_cases h : |f.b| = (f.a : ℤ) ∨ (f.a : ℤ) = f.c
  · simp [reflectReducedForm, h]
  · rcases f with ⟨a, b, c⟩
    simp [reflectReducedForm, h, abs_neg]

theorem reflectReducedForm_mem {D : ℕ+} {f : FormCoefficients} (hf : f ∈ reducedForms D) :
    reflectReducedForm f ∈ reducedForms D := by
  by_cases h : |f.b| = (f.a : ℤ) ∨ (f.a : ℤ) = f.c
  · simpa [reflectReducedForm, h] using hf
  · obtain ⟨hdisc, habs, hac, _, hgcd⟩ := (mem_reducedForms_iff D f).1 hf
    rw [reflectReducedForm, if_neg h, mem_reducedForms_iff]
    refine ⟨by simpa using hdisc, by simpa using habs, hac, ?_, by simpa using hgcd⟩
    intro hb
    exact (h (by simpa only [abs_neg] using hb)).elim

theorem modularInvariant_reflectReducedForm {D : ℕ+} {f : FormCoefficients}
    (hf : f ∈ reducedForms D) :
    modularInvariant (quadraticPoint D (reflectReducedForm f).a (reflectReducedForm f).b) =
      conj (modularInvariant (quadraticPoint D f.a f.b)) := by
  have hf' := (mem_reducedForms_iff D f).1 hf
  by_cases h : |f.b| = (f.a : ℤ) ∨ (f.a : ℤ) = f.c
  · rw [reflectReducedForm, if_pos h, ← modularInvariant_J]
    rcases h with hb | hc
    · have hb' : f.b = (f.a : ℤ) := by
        simpa only [abs_of_nonneg (hf'.2.2.2.1 (Or.inl hb))] using hb
      rw [J_quadraticPoint_eq_T D f.a f.b hb', modularInvariant_smul]
    · rw [J_quadraticPoint_eq_S D f.a f.b f.c hf'.1 hc, modularInvariant_smul]
  · rw [reflectReducedForm, if_neg h, ← modularInvariant_J, J_quadraticPoint]

/-- Complex conjugation fixes the product over all reduced forms. -/
theorem analyticClassPolynomial_map_conj (D : ℕ+) :
    (analyticClassPolynomial D).map (starRingEnd ℂ) = analyticClassPolynomial D := by
  simp only [analyticClassPolynomial, Polynomial.map_prod, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C]
  refine Finset.prod_bij (fun f _ ↦ reflectReducedForm f) ?_ ?_ ?_ ?_
  · exact fun _ hf ↦ reflectReducedForm_mem hf
  · intro a _ b _ h
    exact reflectReducedForm_involutive.injective h
  · intro f hf
    exact ⟨reflectReducedForm f, reflectReducedForm_mem hf, reflectReducedForm_involutive f⟩
  · intro f hf
    rw [modularInvariant_reflectReducedForm hf]

/-- The imaginary part of every coefficient of the analytic class polynomial vanishes. -/
theorem analyticClassPolynomial_coeff_im_zero (D : ℕ+) (n : ℕ) :
    ((analyticClassPolynomial D).coeff n).im = 0 := by
  have h := congrArg (fun P : ℂ[X] ↦ (P.coeff n).im) (analyticClassPolynomial_map_conj D)
  simp only [Polynomial.coeff_map, Complex.conj_im] at h
  linarith only [h]

/-- The analytic class polynomial descends to the real coefficient ring. -/
theorem analyticClassPolynomial_exists_real (D : ℕ+) :
    ∃ P : ℝ[X], P.map Complex.ofRealHom = analyticClassPolynomial D := by
  apply (Polynomial.mem_map_range Complex.ofRealHom).2
  intro n
  refine ⟨((analyticClassPolynomial D).coeff n).re, ?_⟩
  apply Complex.ext
  · simp
  · simp [analyticClassPolynomial_coeff_im_zero]

end GRHArticle.SingularModuli
