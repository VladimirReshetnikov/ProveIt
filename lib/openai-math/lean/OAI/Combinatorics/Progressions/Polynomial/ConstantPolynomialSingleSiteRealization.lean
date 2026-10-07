import OAI.Combinatorics.Progressions.Estimates.PhysicalSingleSiteCommonCover

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped Classical NNReal

variable {X : Type*} {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

theorem exists_constantPolynomial_singleSiteValue
    (Q : ℕ) (hQ : 0 < Q) (y : EuclideanJetLayers U (fun _ => Unit)) :
    ∃ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (hm : ∀ j e, coefficients (poly j) e ∈ U j),
      (∀ j, DegreeLE (1 : X → ℕ) 0 (poly j)) ∧
      ∀ u : X → ℝ, physicalSingleSiteValue U Q poly hm u = y := by
  have hQ0 : (Q : ℝ) ≠ 0 := (Nat.cast_pos.mpr hQ).ne'
  choose x hx using fun j => QuotientAddGroup.mk'_surjective
    (latticeSection (standardEuclideanLattice (J j))
      (euclideanSubspace (U j))).toAddSubgroup (y j ())
  let c : ∀ j, U j := fun j => (Q : ℝ) • euclideanSubspaceArrayEquiv (U j) (x j) ()
  let poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ) := fun j => monomial 0 (c j).val
  have hm : ∀ j e, coefficients (poly j) e ∈ U j := by
    intro j e
    by_cases he : e = 0
    · subst e
      simp [poly]
    · simp [poly, Ne.symm he]
  refine ⟨poly, hm, ?_, ?_⟩
  · intro j e he
    have he0 : e ≠ 0 := by
      intro h
      simp [h] at he
    simp [poly, Ne.symm he0]
  · intro u
    funext j t
    cases t
    rw [physicalSingleSiteValue_eq_mk]
    have hpoint : physicalEuclideanSitePoint U poly hm u j = (Q : ℝ) • x j := by
      apply Subtype.ext
      ext i
      rw [physicalEuclideanSitePoint_apply]
      simp [poly, c, euclideanSubspaceArrayEquiv_apply]
    rw [hpoint, smul_smul, inv_mul_cancel₀ hQ0, one_smul]
    exact hx j

namespace NormalizedPolynomialTwist

variable [Fintype X] {periodCap coverCap : ℝ} {L : ℝ≥0}

theorem eval_commonCover
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (Q : ℕ) (hQ : 0 < Q) (hcover : W.cover ∣ Q) (u : X → ℤ) :
    W.eval N poly u = W.frozenTorus (fun i => (u i : ZMod W.modulus))
      (fun i => (u i : ℝ) / N i)
      (fun a => coveredJetAmbientTorus U (Q / W.cover)
        (physicalSingleSiteValue U Q poly hm (fun i => (u i : ℝ))) ⟨a.1, (), a.2⟩) := by
  rw [physicalSingleSiteValue_commonCover_gridFactorInput U poly hm Q W.cover hQ hcover]
  rfl

theorem frozenSpatialEval_commonCover
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (center : X → ℝ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (Q : ℕ) (hQ : 0 < Q) (hcover : W.cover ∣ Q) (u : X → ℤ) :
    W.frozenSpatialEval center poly u = W.frozenTorus (fun i => (u i : ZMod W.modulus)) center
      (fun a => coveredJetAmbientTorus U (Q / W.cover)
        (physicalSingleSiteValue U Q poly hm (fun i => (u i : ℝ))) ⟨a.1, (), a.2⟩) := by
  rw [physicalSingleSiteValue_commonCover_gridFactorInput U poly hm Q W.cover hQ hcover]
  rfl

end NormalizedPolynomialTwist
end Erdos3.VectorPolynomial

end

end OAI
