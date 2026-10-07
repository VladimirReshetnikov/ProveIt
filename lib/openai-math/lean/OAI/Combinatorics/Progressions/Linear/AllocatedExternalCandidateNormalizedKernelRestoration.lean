/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Dynamics.AllocatedExternalCandidateExponentialFreezingBudget
import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateObservableRestriction

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

theorem conclusion_of_kernel_projection
    (tests : (X → ℤ) → D.Niltest (fullTaggedVariableWeight (X := X) J))
    (htests : ∀ x, (tests x).UnitIntervalValued)
    (hobs : ∀ x, (tests x).observable = observable x)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s)
    (hkernel : K ≤ LinearMap.ker φ.toLinearMap)
    (retained : Finset A.Path) (hsub : retained ⊆ P.productive)
    {newMass newScore : ℝ} (hmass : newMass ≤ A.law.mass retained)
    (hscore : ∀ z : retained, newScore ≤
      (P.candidate ⟨z.val,hsub z.property⟩).score
        (fun x => ((tests x).kernelProjection K hK).observable) weight)
    {outputCost outputMass outputScore Bweight : ℝ}
    (out : (P.restrictObservable (fun x => ((tests x).kernelProjection K hK).observable)
      retained hsub hmass hscore).Conclusion outputCost outputMass outputScore)
    (hOutMass : 0 < outputMass) (hOutScore : 0 < outputScore) (hB : 0 < Bweight)
    (hweight : ∀ x, ‖weight x‖ ≤ Bweight)
    (hσone : ∀ j, σ j ≤ 1) (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ)+1)*R j) ≤ 1/8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val+1) (poly j)) :
    Nonempty (P.Conclusion outputCost (outputScore/(2*Bweight)*outputMass) (outputScore/2)) := by
  let projected := P.restrictObservable (fun x => ((tests x).kernelProjection K hK).observable)
    retained hsub hmass hscore
  have hpos : 0 < A.law.mass out.retained := hOutMass.trans_le out.mass
  have hne : out.retained.Nonempty := by
    apply Finset.nonempty_of_ne_empty
    intro he
    simp [he, FiniteProbabilityWeights.mass] at hpos
  obtain ⟨a₀,ha₀⟩ := hne
  let localLaw (a : A.Path) : FiniteProbabilityWeights A.Site :=
    if ha : a ∈ out.retained then out.siteLaw ⟨a,ha⟩ else out.siteLaw ⟨a₀,ha₀⟩
  have hlaw (a : A.Path) (ha : a ∈ out.retained) :
      localLaw a = out.siteLaw ⟨a,ha⟩ := by
    simp only [localLaw, dite_eq_left ha]
  have hprojected (a : A.Path) (ha : a ∈ out.retained) :
      outputScore ≤ ((localLaw a).complexMean (fun site =>
        weight (A.physical a site) *
        (((tests (A.physical a site)).kernelProjection K hK).withOrbit out.ambient).eval
          (projected.physicalIntegerPoint (A.physical a site)))).re := by
    rw [hlaw a ha]
    exact out.siteLaw_score hσone Cgeo hCgeo hchart hsmall hpoly ⟨a,ha⟩
  obtain ⟨ambient,hmark,zshift,_hshift,_hcoord,_hshiftmark,_hobs,kept,hkept,_hkeptpos,hmassKept,hrestored⟩ :=
    RationalFilteredNilmanifold.Niltest.exists_external_kernelProjection_prescribed_marked_orbit
      tests htests Fmark φ K hK hkernel out.ambient marked out.marked
      A.law out.retained hpos localLaw A.physical
      (fun a site => projected.physicalIntegerPoint (A.physical a site))
      (fun a site => weight (A.physical a site)) hB hOutScore
      (fun a _ site => hweight (A.physical a site)) hprojected
  refine ⟨{
    ambient := ambient
    marked := hmark
    retained := kept
    subset := fun a ha => hsub (out.subset (hkept ha))
    mass := (mul_le_mul_of_nonneg_left out.mass (by positivity)).trans hmassKept
    step := fun a => out.step ⟨a.val,hkept a.property⟩
    step_pos := fun a => out.step_pos ⟨a.val,hkept a.property⟩
    slice := fun a => out.slice ⟨a.val,hkept a.property⟩
    dense := fun a => out.dense ⟨a.val,hkept a.property⟩
    inside := fun a => out.inside ⟨a.val,hkept a.property⟩
    score := ?_ }⟩
  intro a
  let old : out.retained := ⟨a.val,hkept a.property⟩
  have hs := hrestored a.val a.property
  rw [hlaw a.val old.property] at hs
  have he : ((out.siteLaw old).complexMean (fun site =>
      weight (A.physical a.val site) * ((tests (A.physical a.val site)).withOrbit ambient).eval
        (projected.physicalIntegerPoint (A.physical a.val site)))).re =
      P.ambientScore ambient ⟨a.val,hsub (out.subset old.property)⟩
        (out.slice old).integerPoints := by
    change ((out.siteLaw old).complexMean (fun site => weight (A.physical a.val site) *
      (tests (A.physical a.val site)).observable (P.ambientPhysicalValue ambient (A.physical a.val site)))).re = _
    simp_rw [hobs]
    rw [P.ambientScore_eq_physical hσone Cgeo hCgeo hchart hsmall hpoly ambient
      ⟨a.val,hsub (out.subset old.property)⟩ _ (out.inside old)]
    exact congrArg Complex.re (out.siteLaw_complexMean_physical old (fun x =>
      weight x * observable x (P.ambientPhysicalValue ambient x)))
  exact hs.trans_eq he

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

private theorem exp_neg_add_two_le_half (p : ℝ) :
    Real.exp (-(p+2)) ≤ Real.exp (-p)/2 := by
  have hlog : Real.log (2 : ℝ) ≤ 2 :=
    (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)).trans (by norm_num)
  calc
    _ ≤ Real.exp (-p-Real.log 2) := Real.exp_le_exp.mpr (by linarith only [hlog])
    _ = _ := by rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

theorem kernel_restoration_exp_budget {p : ℝ} (hp : 0 ≤ p) :
    p ≤ 3*p+2 ∧
    Real.exp (-(3*p+2)) ≤ Real.exp (-p)/(2*Real.exp p)*Real.exp (-p) ∧
    Real.exp (-(3*p+2)) ≤ Real.exp (-p)/2 := by
  have hmass : Real.exp (-p)/(2*Real.exp p)*Real.exp (-p) = Real.exp (-(3*p))/2 := by
    rw [mul_comm (2 : ℝ) (Real.exp p), div_mul_eq_div_div, ← Real.exp_sub,
      div_mul_eq_mul_div, ← Real.exp_add]
    congr 2
    ring
  refine ⟨by linarith only [hp], ?_, ?_⟩
  · rw [hmass]
    exact exp_neg_add_two_le_half (3*p)
  · exact (Real.exp_le_exp.mpr (by linarith only [hp] : -(3*p+2) ≤ -(p+2))).trans
      (exp_neg_add_two_le_half p)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

theorem conclusion_of_kernel_projection_normalized
    (tests : (X → ℤ) → D.Niltest (fullTaggedVariableWeight (X := X) J))
    (htests : ∀ x, (tests x).UnitIntervalValued)
    (hobs : ∀ x, (tests x).observable = observable x)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s)
    (hkernel : K ≤ LinearMap.ker φ.toLinearMap)
    (retained : Finset A.Path) (hsub : retained ⊆ P.productive)
    {newMass newScore : ℝ} (hmass : newMass ≤ A.law.mass retained)
    (hscore : ∀ z : retained, newScore ≤
      (P.candidate ⟨z.val,hsub z.property⟩).score
        (fun x => ((tests x).kernelProjection K hK).observable) weight)
    {p : ℝ} (hp : 0 ≤ p)
    (out : (P.restrictObservable (fun x => ((tests x).kernelProjection K hK).observable)
      retained hsub hmass hscore).Conclusion p (Real.exp (-p)) (Real.exp (-p)))
    (hweight : ∀ x, ‖weight x‖ ≤ Real.exp p)
    (hσone : ∀ j, σ j ≤ 1) (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ)+1)*R j) ≤ 1/8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val+1) (poly j)) :
    Nonempty (P.Conclusion (3*p+2) (Real.exp (-(3*p+2))) (Real.exp (-(3*p+2)))) := by
  obtain ⟨restored⟩ := P.conclusion_of_kernel_projection tests htests hobs K hK hkernel
    retained hsub hmass hscore out (Real.exp_pos _) (Real.exp_pos _) (Real.exp_pos p)
    hweight hσone Cgeo hCgeo hchart hsmall hpoly
  obtain ⟨hcost, hmass', hscore'⟩ := kernel_restoration_exp_budget hp
  exact ⟨restored.mono hcost hmass' hscore'⟩

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
