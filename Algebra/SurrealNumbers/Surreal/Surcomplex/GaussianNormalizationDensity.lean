import Surreal.Surcomplex.GaussianNormalizationEmbedding
import Surreal.Surcomplex.GaussianAlgebraAbsorption

/-!
# Density of the actual Gaussian normalization

The density and properness clauses of `osq:nm:thm:complexnormal`.
Real integral approximations in both coordinates give approximations
in every positive surreal-modulus ball in the native surcomplex topology.
-/

universe u
namespace Surreal.Surcomplex
open Foundations
noncomputable section

/-- Every surcomplex has a Gaussian-integral approximation at every positive surreal tolerance. -/
theorem gaussianOmnific_integral_approximation (z : Surcomplex.{u})
    (ε : SignSequence.{u}) (hε : 0 < ε) :
    ∃ w : integralClosure GaussianOmnificInteger Surcomplex.{u}, modulus (z - w) < ε := by
  obtain ⟨x, hx0, hx⟩ := SignSequence.omnific_integral_approximation z.re (ε / 2) (by positivity)
  obtain ⟨y, hy0, hy⟩ := SignSequence.omnific_integral_approximation z.im (ε / 2) (by positivity)
  let w : Surcomplex.{u} := ofReal (x : SignSequence) + ofReal (y : SignSequence) * I
  have hw : IsIntegral GaussianOmnificInteger w :=
    (gaussianOmnific_isIntegral_ofReal x.property).add
      ((gaussianOmnific_isIntegral_ofReal y.property).mul gaussianOmnific_I_isIntegral)
  refine ⟨⟨w, hw⟩, ?_⟩
  have hre : (z - w).re = z.re - (x : SignSequence) := by simp [w]
  have him : (z - w).im = z.im - (y : SignSequence) := by simp [w]
  apply (modulus_le_abs_re_add_abs_im (z - w)).trans_lt
  rw [hre, him, abs_of_nonneg hx0, abs_of_nonneg hy0]
  linarith

/-- Gaussian normalization is dense in the actual surreal-modulus topology. -/
theorem gaussianOmnific_integralClosure_dense :
    Dense (integralClosure GaussianOmnificInteger Surcomplex.{u} : Set Surcomplex) := by
  intro z
  apply (mem_closure_iff_nhds_basis (nhds_hasBasis_modulus z)).mpr
  intro ε hε
  obtain ⟨w, hw⟩ := gaussianOmnific_integral_approximation z ε hε
  refine ⟨w, w.property, ?_⟩
  change modulus ((w : Surcomplex) - z) < ε
  rw [← neg_sub z (w : Surcomplex), modulus_neg]
  exact hw

/-- The topological closure of Gaussian normalization is the whole actual surcomplex field. -/
theorem gaussianOmnific_integralClosure_closure :
    closure (integralClosure GaussianOmnificInteger Surcomplex.{u} : Set Surcomplex) = Set.univ :=
  gaussianOmnific_integralClosure_dense.closure_eq

/-- The nonintegral half keeps Gaussian normalization a proper subalgebra of the ambient field. -/
theorem gaussianOmnific_integralClosure_lt_top :
    integralClosure GaussianOmnificInteger Surcomplex.{u} < ⊤ := by
  rw [← gaussianOmnific_completeIntegralClosure_eq_top]
  exact gaussianOmnific_integralClosure_lt_completeIntegralClosure

end
end Surreal.Surcomplex
