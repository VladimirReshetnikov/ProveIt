import OAI.Combinatorics.Progressions.Estimates.AllocatedAnchoredRecoveredSource
import OAI.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleCongruenceOutput

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped Classical BigOperators Matrix

variable {K X : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

theorem affineCoefficientCoverSample_emptyJet
    (root : K → ℤ) (D : Matrix Empty K ℤ) (q : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hm : ∀ j a, coefficients (poly j) a ∈ U j)
    (z : Option K × X → ℤ) :
    euclideanCoefficientJetMap U root D (fun _ (_ : Unit) => ∅)
      (affineCoefficientCoverSample U poly hm q (fun k x => (z (k,x) : ℝ))) =
      physicalSingleSiteValue U q poly hm (physicalAffineSite root z) := by
  let f : Option K → X → ℝ := fun k x => (z (k,x) : ℝ)
  have hpoint : (fun x => MvPolynomial.aeval (fun k => (root k : ℝ))
      (affineParameterSubstitution f x)) = physicalAffineSite root z := by
    funext x
    rw [affineParameterSubstitution_eval]
    simp [physicalAffineSite, integerSiteValue, Fintype.sum_option, Finset.sum_apply,
      zsmul_eq_mul, mul_comm, f]
  funext j t
  cases t
  let v := substitute (affineParameterSubstitution f)
    (restrictCoefficients (U j) (poly j) (hm j))
  have hv : DegreeLE (1 : K → ℕ) (j.val + 1) v :=
    degreeLE_substitute_affine (affineParameterSubstitution f)
      (affineParameterSubstitution_degree f) _
      (degreeLE_restrictCoefficients (U j) (poly j) (hm j) (hp j))
  have he := congrFun (siteEvaluation_bounded_coefficients (fun _ : Unit => root) v hv) ()
  change eval (fun k => (root k : ℝ)) v =
    ∑ e, (boundedSiteMatrix (j.val + 1) (fun _ : Unit => root) () e : ℝ) • coefficients v e.val at he
  dsimp only [v] at he
  rw [eval_substitute, hpoint] at he
  change (euclideanSubspaceTorusEquiv (U j)).symm
    (arrayCoordinateTorus (U j)
      (coefficientBooleanJetTorusMap U root D (fun _ (_ : Unit) => ∅)
        (affineCoefficientCoverSample U poly hm q f) j) ()) = _
  rw [affineCoefficientCoverSample, coefficientBooleanJetTorusMap_mk,
    arrayCoordinateTorus_mk]
  apply congrArg (euclideanSubspaceTorusEquiv (U j)).symm
  apply congrArg (QuotientAddGroup.mk' (subspaceArrayIntegerLattice Unit (U j)))
  funext t
  change (∑ e, (boundedCoefficientJetMatrix root D (j.val + 1)
    (fun _ : Unit => ∅) () e : ℝ) •
      ((q : ℝ)⁻¹ • coefficients v e.val)) = _
  simp_rw [boundedCoefficientJetMatrix_empty, smul_comm _ ((q : ℝ)⁻¹)]
  rw [← Finset.smul_sum, ← he]

section Allocated
variable {G : Type*} [Fintype G]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedRecoveredSample_site_chart
    (q : ℕ) [NeZero q]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hm : ∀ j a, coefficients (poly j) a ∈ U j)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hbase : canonicalCoefficientSample U b hb o sample =
      affineSampleCoefficientTorus U poly hm (fun k x => (noise (k,x) : ℝ)))
    (hsmall : ∀ a, |coefficientSamplerAmbientPoint U b o sample a| < 1/2)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hread : ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop,
      coefficientDeckChartEvent U bW b hb o q event
        (affineCoefficientCoverSample U poly hm q (fun k x => (noise (k,x) : ℝ))) ↔
      event (allocatedReadCoefficientChartResidues (fun i => (read i : ZMod q))))
    (x : G → IntegerScalarCubeBox Empty S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U b S))
    (j : Fin m) :
    physicalSingleSiteValue U q poly hm
      (fun z => (integerPhysicalSite (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y) noise z : ℝ)) j () =
      normalizedCoveredChart (euclideanSubspace (U j)) (b j) (hb j) (bW j) q
        (orthonormalMixedChart (o j) (allocatedOriginalSamplePhysicalMixedValue B U b S sample x y j),
          integerResidueMap (E j) q
            (allocatedOriginalSampleDeckValue B U b S (allocatedReadDeck read) x y j)) := by
  have hprojection : quotientIntegerCover (coefficientIntegerLattice U) q
      (affineCoefficientCoverSample U poly hm q (fun k z => (noise (k,z) : ℝ))) =
      canonicalCoefficientSample U b hb o sample := by
    rw [affineCoefficientCoverSample_projection U poly hm q (NeZero.pos q)]
    exact hbase.symm
  have hjet := coefficientEventRead_jet_chart U bW b hb o
    (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
    (allocatedPhysicalCubeDirections B U b S x y) (fun _ (_ : Unit) => ∅) q sample
    (affineCoefficientCoverSample U poly hm q (fun k z => (noise (k,z) : ℝ)))
    hprojection hsmall (allocatedReadCoefficientChartResidues (fun i => (read i : ZMod q))) hread
  rw [affineCoefficientCoverSample_emptyJet U _ _ q poly hp hm noise] at hjet
  have h := congrFun (congrFun hjet j) ()
  simp_rw [integerPhysicalSite_cast_apply]
  change _ = normalizedCoveredChart (euclideanSubspace (U j)) (b j) (hb j) (bW j) q
    (orthonormalMixedChart (o j) (allocatedOriginalSamplePhysicalMixedValue B U b S sample x y j),
      integerResidueMap (E j) q (allocatedOriginalSampleDeckValue B U b S (allocatedReadDeck read) x y j))
  rw [← allocatedOriginalSampleDeckValue_residue B U b S (allocatedReadDeck read) q x y j]
  exact h

theorem allocatedRecoveredSample_site_chart_base
    (q : ℕ) [NeZero q]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hm : ∀ j a, coefficients (poly j) a ∈ U j)
    (base : X → ℤ)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hbase : canonicalCoefficientSample U b hb o sample =
      affineSampleCoefficientTorus U poly hm (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base + noise) (k,x) : ℝ)))
    (hsmall : ∀ a, |coefficientSamplerAmbientPoint U b o sample a| < 1/2)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hread : ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop,
      coefficientDeckChartEvent U bW b hb o q event
        (affineCoefficientCoverSample U poly hm q (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base + noise) (k,x) : ℝ))) ↔
      event (allocatedReadCoefficientChartResidues (fun i => (read i : ZMod q))))
    (x : G → IntegerScalarCubeBox Empty S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U b S))
    (j : Fin m) :
    physicalSingleSiteValue U q poly hm
      (fun z => (base z + integerPhysicalSite (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y) noise z : ℝ)) j () =
      normalizedCoveredChart (euclideanSubspace (U j)) (b j) (hb j) (bW j) q
        (orthonormalMixedChart (o j) (allocatedOriginalSamplePhysicalMixedValue B U b S sample x y j),
          integerResidueMap (E j) q
            (allocatedOriginalSampleDeckValue B U b S (allocatedReadDeck read) x y j)) := by
  simpa only [integerPhysicalSite_baseTranslation_add, Pi.add_apply, Int.cast_add] using
    allocatedRecoveredSample_site_chart U B bW b hb o S q poly hp hm
      (integerBaseTranslation (K := LayerSamplerVariables G I n B) base + noise) sample hbase hsmall read hread x y j

end Allocated
end Erdos3.VectorPolynomial

end

end OAI
