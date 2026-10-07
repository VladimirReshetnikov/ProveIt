import OAI.Combinatorics.Progressions.Probability.PreparedModularGeneralCenteredLaw

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped Classical

variable {m : ℕ} {X : Type*} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
variable (c : ∀ j, U j) (a : X → ℤ)

noncomputable def allocatedCenteredConditionalPolynomial (j : Fin m) :
    VectorPolynomial X ℝ (J j → ℝ) :=
  translate (fun i => (a i : ℝ)) (subtractConstant (c j).val (poly j))

omit [∀ j, Fintype (J j)] in
include hmem in
theorem allocatedCenteredConditionalPolynomial_mem (j : Fin m) (e : X →₀ ℕ) :
    coefficients (allocatedCenteredConditionalPolynomial U poly c a j) e ∈ U j :=
  coefficients_translate_mem (U j) _ _
    (coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j)) e

omit [∀ j, Fintype (J j)] in
theorem allocatedCenteredConditionalPolynomial_degree
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)) (j : Fin m) :
    DegreeLE (1 : X → ℕ) (j.val + 1) (allocatedCenteredConditionalPolynomial U poly c a j) :=
  degreeLE_translate _ (fun _ => by norm_num) _ _ ((hp j).subtractConstant _)

theorem allocatedCenteredConditionalPolynomial_rank
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (H : X → ℝ) (Rrank : ℝ) (j : Fin m) :
    HasLayerSamplingRank (j.val + 1) H Rrank (U j)
      (allocatedCenteredConditionalPolynomial U poly c a j) ↔
      HasLayerSamplingRank (j.val + 1) H Rrank (U j) (poly j) := by
  unfold allocatedCenteredConditionalPolynomial
  rw [hasLayerSamplingRank_translate_iff _ _ _ _ _ _ ((hp j).subtractConstant _),
    hasLayerSamplingRank_subtractConstant_iff (by omega)]

variable {G : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ x, Fintype (B x)]
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

omit [Fintype X] in
theorem allocatedCenteredConditionalPolynomial_density
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (hc : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => c s.1))))
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    allocatedCoefficientDensity B U b hb o hR hσ S
      (affineSampleCoefficientTorus U (allocatedCenteredConditionalPolynomial U poly c a)
        (allocatedCenteredConditionalPolynomial_mem U poly hmem c a)
        (fun k x => (z (k,x) : ℝ))) =
      allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center a z := by
  exact congrFun (congrFun
    (allocatedJointBaseDensity_subtractConstant_centered B U b hb o hR hσ S poly hmem center c hc) a) z

end Erdos3.VectorPolynomial

end

end OAI
