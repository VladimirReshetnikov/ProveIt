/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Supply per-layer measurable-addition instances explicitly in the common-cover
measure-preservation proof for Lean 4.32. All theorem statements are unchanged. -/
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleFullSliceLipschitz
import OAI.Combinatorics.Progressions.Geometry.AllocatedFullSiteSupport
import OAI.Combinatorics.Progressions.Geometry.NormalizedTwistSpatialPartition
import OAI.Combinatorics.Progressions.Linear.PhysicalSiteProjection
import OAI.Combinatorics.Progressions.Sampling.CoefficientUniformPerturbationSampling

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

theorem coefficientLayerArray_affineSample {I K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (x : Option K → I → ℝ) (j : Fin m) :
    coefficientLayerArray U j (affineSampleCoefficientArray U p hm x) =
      fun d => coefficients (substitute (affineParameterSubstitution x)
        (restrictCoefficients (U j) (p j) (hm j))) d.val := rfl

theorem coefficientSiteTorusMap_coverSample {I K : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (difference : Fin q → K → ℤ) (D : ℕ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (x : Option K → I → ℝ) :
    coefficientSiteTorusMap U (fun s k => affineSite root difference s (some k))
      (affineCoefficientCoverSample U p hm D x) = affineCoveredSiteSample U root difference D p hm x := by
  funext j
  rw [affineCoefficientCoverSample, coefficientSiteTorusMap_mk]
  let v : VectorPolynomial K ℝ (U j) :=
    substitute (affineParameterSubstitution x) (restrictCoefficients (U j) (p j) (hm j))
  have hv : DegreeLE (1 : K → ℕ) (j.val + 1) v :=
    degreeLE_substitute_affine (affineParameterSubstitution x) (affineParameterSubstitution_degree x)
    (restrictCoefficients (U j) (p j) (hm j))
    (degreeLE_restrictCoefficients (U j) (p j) (hm j) (hp j))
  have he := siteEvaluation_bounded_coefficients
    (fun s k => affineSite root difference s (some k)) v hv
  rw [map_smul, coefficientLayerArray_affineSample, map_smul]
  exact congrArg (fun y : Finset (Fin q) → U j =>
    QuotientAddGroup.mk' (subspaceArrayIntegerLattice (Finset (Fin q)) (U j)) ((D : ℝ)⁻¹ • y)) he.symm

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

private theorem root_coe_sum {A : Type*} [Fintype A] (a : A → ℝ) :
    ((∑ t, a t : ℝ) : UnitAddCircle) = ∑ t, (a t : UnitAddCircle) :=
  map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) a Finset.univ

variable {K : Type*} [Fintype K] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]

noncomputable def coefficientAmbientRoot (root : K → ℤ)
    (z : CoefficientAmbientIndex K J → UnitAddCircle) : (Σ j, J j) → UnitAddCircle :=
  fun a => ∑ e : BoundedCoefficientExponent K (a.1.val + 1),
    boundedSiteMatrix (a.1.val + 1) (fun _ : Unit => root) () e • z ⟨⟨a.1,e⟩,a.2⟩

noncomputable def coefficientAmbientRootLip (m : ℕ) (root : K → ℤ) : ℝ≥0 :=
  ∑ j : Fin m, ∑ e : BoundedCoefficientExponent K (j.val + 1),
    ‖boundedSiteMatrix (j.val + 1) (fun _ : Unit => root) () e‖₊

theorem coefficientAmbientRoot_lipschitz (root : K → ℤ) :
    LipschitzWith (coefficientAmbientRootLip m root) (coefficientAmbientRoot (J := J) root) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  apply (dist_pi_le_iff (by positivity)).mpr
  rintro ⟨j, i⟩
  change dist (∑ e, boundedSiteMatrix (j.val + 1) (fun _ : Unit => root) () e • z ⟨⟨j,e⟩,i⟩)
    (∑ e, boundedSiteMatrix (j.val + 1) (fun _ : Unit => root) () e • w ⟨⟨j,e⟩,i⟩) ≤ _
  calc
    _ ≤ ∑ e, dist
        (boundedSiteMatrix (j.val + 1) (fun _ : Unit => root) () e • z ⟨⟨j,e⟩,i⟩)
        (boundedSiteMatrix (j.val + 1) (fun _ : Unit => root) () e • w ⟨⟨j,e⟩,i⟩) :=
      dist_sum_sum_le _ _ _
    _ ≤ ∑ e, ‖boundedSiteMatrix (j.val + 1) (fun _ : Unit => root) () e‖ * dist z w := by
      apply Finset.sum_le_sum
      intro e _
      rw [dist_eq_norm, ← smul_sub]
      exact (norm_zsmul_le _ _).trans (mul_le_mul_of_nonneg_left
        (by simpa only [dist_eq_norm] using dist_le_pi_dist z w ⟨⟨j,e⟩,i⟩) (norm_nonneg _))
    _ = (∑ e, ‖boundedSiteMatrix (j.val + 1) (fun _ : Unit => root) () e‖) * dist z w :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ dist_nonneg
      simpa only [coefficientAmbientRootLip, NNReal.coe_sum, coe_nnnorm] using
        (Finset.single_le_sum (s := Finset.univ)
          (f := fun j : Fin m => ∑ e : BoundedCoefficientExponent K (j.val + 1),
            ‖boundedSiteMatrix (j.val + 1) (fun _ : Unit => root) () e‖)
          (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Finset.mem_univ j))

omit [∀ j, Fintype (J j)] in
theorem coefficientAmbientRoot_mk (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (y : CoefficientArray (K := K) U) (a : Σ j, J j) :
    coefficientAmbientRoot root
      (coefficientAmbientTorus U (QuotientAddGroup.mk' (coefficientIntegerLattice U) y)) a =
      ((∑ e : BoundedCoefficientExponent K (a.1.val + 1),
        (boundedSiteMatrix (a.1.val + 1) (fun _ : Unit => root) () e : ℝ) *
          (y ⟨a.1,e⟩).val a.2 : ℝ) : UnitAddCircle) := by
  simp only [coefficientAmbientRoot, coefficientAmbientTorus_mk]
  rw [root_coe_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [← zsmul_eq_mul, AddCircle.coe_zsmul]

omit [∀ j, Fintype (J j)] in
theorem coefficientAmbientRoot_sample {X : Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j) (z : Option K × X → ℤ) :
    coefficientAmbientRoot root (coefficientAmbientTorus U
      (affineCoefficientCoverSample U poly hm d (fun k x => (z (k,x) : ℝ)))) =
      physicalGridFactorInput d poly (physicalAffineSite root z) := by
  let b : Option K → X → ℝ := fun k x => (z (k,x) : ℝ)
  have hpoint : (fun x => MvPolynomial.aeval (fun k => (root k : ℝ))
      (affineParameterSubstitution b x)) = physicalAffineSite root z := by
    funext x
    rw [affineParameterSubstitution_eval]
    simp [physicalAffineSite, integerSiteValue, Fintype.sum_option, Finset.sum_apply,
      zsmul_eq_mul, mul_comm, b]
  funext a
  rcases a with ⟨j, i⟩
  have hv := degreeLE_substitute_affine (affineParameterSubstitution b)
    (affineParameterSubstitution_degree b) (poly j) (hp j)
  have he := congrFun (congrFun (siteEvaluation_bounded_coefficients
    (fun _ : Unit => root) (substitute (affineParameterSubstitution b) (poly j)) hv) ()) i
  change eval (fun k => (root k : ℝ))
      (substitute (affineParameterSubstitution b) (poly j)) i =
    (∑ e : BoundedCoefficientExponent K (j.val + 1),
      (boundedSiteMatrix (j.val + 1) (fun _ : Unit => root) () e : ℝ) •
        coefficients (substitute (affineParameterSubstitution b) (poly j)) e.val) i at he
  rw [eval_substitute, hpoint] at he
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at he
  rw [affineCoefficientCoverSample, coefficientAmbientRoot_mk]
  change ((∑ e : BoundedCoefficientExponent K (j.val + 1),
    (boundedSiteMatrix (j.val + 1) (fun _ : Unit => root) () e : ℝ) *
      ((d : ℝ)⁻¹ * (affineSampleCoefficientArray U poly hm b ⟨j,e⟩).val i) : ℝ) : UnitAddCircle) =
    ((eval (physicalAffineSite root z) (poly j) i / d : ℝ) : UnitAddCircle)
  simp only [affineSampleCoefficientArray_val]
  congr 1
  rw [he, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _
  ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem boundedCoefficientJetMatrix_empty {α K : Type*} [DecidableEq α] [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (h : ℕ)
    (e : VectorPolynomial.BoundedCoefficientExponent K h) :
    boundedCoefficientJetMatrix root D h (fun _ : Unit => ∅) () e =
      VectorPolynomial.boundedSiteMatrix h (fun _ : Unit => root) () e := by
  simp [boundedCoefficientJetMatrix, boundedDegreeIntegerJetMatrix,
    boundedCoefficientIntegerExponentEquiv, integerJetMatrix, booleanCoefficient,
    integerAffineCube, VectorPolynomial.boundedSiteMatrix, MvPolynomial.eval_monomial]

namespace VectorPolynomial

variable {K : Type*} [Fintype K] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]

theorem coefficientAmbientRoot_eq_emptyJet {α : Type*} [Fintype α] [DecidableEq α]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (D : Matrix α K ℤ)
    (t : CoefficientTorus (K := K) U) :
    coefficientAmbientRoot root (coefficientAmbientTorus U t) =
      fun a => coveredJetAmbientTorus U 1
        (euclideanCoefficientJetMap U root D (fun _ (_ : Unit) => ∅) t)
        ⟨a.1, (), a.2⟩ := by
  funext a
  simp only [coefficientAmbientRoot, coveredJetAmbientTorus_coefficient,
    Nat.cast_one, one_mul, boundedCoefficientJetMatrix_empty]

theorem coefficientAmbientRoot_eq_oneSiteJet
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ)
    (t : CoefficientTorus (K := K) U) :
    coefficientAmbientRoot root (coefficientAmbientTorus U t) =
      fun a => coveredJetAmbientTorus U 1
        (euclideanCoefficientJetMap U root (0 : Matrix Empty K ℤ)
          (fun _ (_ : Unit) => ∅) t) ⟨a.1, (), a.2⟩ :=
  coefficientAmbientRoot_eq_emptyJet U root (0 : Matrix Empty K ℤ) t

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S))

noncomputable def allocatedOriginalSamplePhysicalMixedValue
    (j : Fin m) : (I j → ℝ) × (Fin (n j) → ℤ) :=
  mixedArrayRegroup (I j) (Fin (n j)) Unit
    (canonicalCoefficientJetArrays
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y)
      (fun (_ : Fin m) (_ : Unit) => (∅ : Finset Empty)) sample j) ()

theorem allocatedOriginalSamplePhysicalMixedValue_real (j : Fin m) (i : I j) :
    (allocatedOriginalSamplePhysicalMixedValue B U basis S sample x y j).1 i =
      MvPolynomial.eval (fun v =>
        (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y v : ℝ))
        (monomialArrayPolynomial Subtype.val ((sample j).1 i)) := by
  rw [monomialArrayPolynomial_eval]
  change (∑ d, (boundedCoefficientJetMatrix
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y)
      (j.val + 1) (fun _ : Unit => ∅) () d : ℝ) * (sample j).1 i d) = _
  apply Finset.sum_congr rfl
  intro d _
  rw [boundedCoefficientJetMatrix_empty]
  simp only [boundedSiteMatrix, Finsupp.prod, Int.cast_prod, Int.cast_pow]
  exact mul_comm _ _

theorem allocatedOriginalSamplePhysicalMixedValue_integer (j : Fin m) (i : Fin (n j)) :
    (allocatedOriginalSamplePhysicalMixedValue B U basis S sample x y j).2 i =
      MvPolynomial.eval (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
        (∑ d, MvPolynomial.monomial d.val ((sample j).2 i d)) := by
  simp only [map_sum, MvPolynomial.eval_monomial, Finsupp.prod]
  change (∑ d, boundedCoefficientJetMatrix
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y)
      (j.val + 1) (fun _ : Unit => ∅) () d * (sample j).2 i d) = _
  apply Finset.sum_congr rfl
  intro d _
  rw [boundedCoefficientJetMatrix_empty]
  exact mul_comm _ _

theorem allocatedOriginalSamplePhysicalMixedValue_integer_cast
    (j : Fin m) (i : Fin (n j)) :
    ((allocatedOriginalSamplePhysicalMixedValue B U basis S sample x y j).2 i : ℝ) =
      MvPolynomial.eval (fun v =>
        (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y v : ℝ))
        (monomialArrayPolynomial Subtype.val (fun d => ((sample j).2 i d : ℝ))) := by
  rw [allocatedOriginalSamplePhysicalMixedValue_integer]
  simp only [monomialArrayPolynomial, map_sum, MvPolynomial.eval_monomial,
    Finsupp.prod, Int.cast_sum, Int.cast_mul, Int.cast_prod, Int.cast_pow]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {X K : Type*} [Fintype X] [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {L : ℝ≥0}

noncomputable def frozenAmbientRootObservable
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (residue : X → ZMod W.modulus) (center : X → ℝ) (root : K → ℤ)
    (z : CoefficientAmbientIndex K J → UnitAddCircle) : ℂ :=
  W.frozenTorus residue center (coefficientAmbientRoot root z)

theorem norm_frozenAmbientRootObservable_le
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (residue : X → ZMod W.modulus) (center : X → ℝ) (root : K → ℤ)
    (z : CoefficientAmbientIndex K J → UnitAddCircle) :
    ‖W.frozenAmbientRootObservable residue center root z‖ ≤ 1 :=
  W.norm_frozenTorus_le _ _ _

theorem frozenAmbientRootObservable_lipschitz
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (residue : X → ZMod W.modulus) (center : X → ℝ) (root : K → ℤ) :
    LipschitzWith (L * coefficientAmbientRootLip m root)
      (W.frozenAmbientRootObservable residue center root) :=
  (W.frozenTorus_lipschitz residue center).comp (coefficientAmbientRoot_lipschitz root)

theorem frozenAmbientRootObservable_sample
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (residue : X → ZMod W.modulus) (center : X → ℝ) (root : K → ℤ)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j) (z : Option K × X → ℤ) :
    W.frozenAmbientRootObservable residue center root (coefficientAmbientTorus U
      (affineCoefficientCoverSample U poly hm W.cover (fun k x => (z (k,x) : ℝ)))) =
      W.frozenTorus residue center (physicalGridFactorInput W.cover poly (physicalAffineSite root z)) := by
  unfold frozenAmbientRootObservable
  rw [coefficientAmbientRoot_sample U root W.cover poly hp hm]

noncomputable def rootResidue (modulus : ℕ) (root : K → ℤ)
    (r : ColumnResiduePattern (Option K) X (fun _ => modulus)) : X → ZMod modulus :=
  fun x => r (none,x) + ∑ k, (root k : ZMod modulus) * r (some k,x)

omit [Fintype X] in
theorem integerPhysicalSite_residue (modulus : ℕ) (root : K → ℤ)
    (r : ColumnResiduePattern (Option K) X (fun _ => modulus)) (z : Option K × X → ℤ)
    (hz : columnResiduePattern (fun _ : X => modulus) z = r) :
    (fun x => (integerPhysicalSite root z x : ZMod modulus)) = rootResidue modulus root r := by
  funext x
  simp only [integerPhysicalSite, Int.cast_add, Int.cast_sum, Int.cast_mul, rootResidue]
  congr 1
  · exact congrFun hz (none,x)
  · apply Finset.sum_congr rfl
    intro k _
    exact congrArg (fun t => (root k : ZMod modulus) * t) (congrFun hz (some k,x))

theorem frozenSpatialEval_integerPhysicalSite_of_residue
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (center : X → ℝ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (root : K → ℤ)
    (r : ColumnResiduePattern (Option K) X (fun _ => W.modulus)) (z : Option K × X → ℤ)
    (hz : columnResiduePattern (fun _ : X => W.modulus) z = r) :
    W.frozenSpatialEval center poly (integerPhysicalSite root z) =
      W.frozenTorus (rootResidue W.modulus root r) center
        (physicalGridFactorInput W.cover poly (physicalAffineSite root z)) := by
  simp only [frozenSpatialEval, integerPhysicalSite_cast_apply,
    integerPhysicalSite_residue W.modulus root r z hz]

theorem selected_weighted_frozenSpatialEval_root_eq
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (center : X → ℝ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (root : K → ℤ)
    (r : ColumnResiduePattern (Option K) X (fun _ => W.modulus))
    (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ => W.modulus) {r} V z)
    (weight : (Option K × X → ℤ) → ℂ) :
    (∑' z : Option K × X → ℤ,
      ((selectedResidueSmoothPMF (fun _ => W.modulus) {r} V hV hZ z).toReal : ℂ) *
        (weight z * W.frozenSpatialEval center poly (integerPhysicalSite root z))) =
      ∑' z : Option K × X → ℤ,
        ((selectedResidueSmoothPMF (fun _ => W.modulus) {r} V hV hZ z).toReal : ℂ) *
          (weight z * W.frozenTorus (rootResidue W.modulus root r) center
            (physicalGridFactorInput W.cover poly (physicalAffineSite root z))) := by
  apply tsum_congr
  intro z
  by_cases hz : columnResiduePattern (fun _ : X => W.modulus) z = r
  · rw [W.frozenSpatialEval_integerPhysicalSite_of_residue center poly root r z hz]
  · have hweight : (selectedResidueSmoothPMF (fun _ => W.modulus) {r} V hV hZ z).toReal = 0 := by
      rw [selectedResidueSmoothPMF_toReal]
      simp only [selectedResidueSmoothWeight, Finset.mem_singleton, hz, ite_false, zero_div]
    simp only [hweight, Complex.ofReal_zero, zero_mul]

theorem selected_frozenSpatialEval_root_eq
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (center : X → ℝ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (root : K → ℤ)
    (r : ColumnResiduePattern (Option K) X (fun _ => W.modulus))
    (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ => W.modulus) {r} V z) :
    (∑' z : Option K × X → ℤ,
      ((selectedResidueSmoothPMF (fun _ => W.modulus) {r} V hV hZ z).toReal : ℂ) *
        W.frozenSpatialEval center poly (integerPhysicalSite root z)) =
      ∑' z : Option K × X → ℤ,
        ((selectedResidueSmoothPMF (fun _ => W.modulus) {r} V hV hZ z).toReal : ℂ) *
          W.frozenTorus (rootResidue W.modulus root r) center
            (physicalGridFactorInput W.cover poly (physicalAffineSite root z)) := by
  simpa only [one_mul] using
    W.selected_weighted_frozenSpatialEval_root_eq center poly root r V hV hZ (fun _ => 1)

theorem selected_density_frozenSpatialEval_root_eq
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (center : X → ℝ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (root : K → ℤ)
    (r : ColumnResiduePattern (Option K) X (fun _ => W.modulus))
    (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ => W.modulus) {r} V z)
    (D : (Option K × X → ℤ) → ℝ) (hD0 : ∀ z, 0 ≤ D z)
    (hD : 0 < selectedResidueDensityMass (fun _ => W.modulus) {r} V D) :
    (∑' z : Option K × X → ℤ,
      ((selectedResidueDensityPMF (fun _ => W.modulus) {r} V hV hZ D hD0 hD z).toReal : ℂ) *
        W.frozenSpatialEval center poly (integerPhysicalSite root z)) =
      ∑' z : Option K × X → ℤ,
        ((selectedResidueDensityPMF (fun _ => W.modulus) {r} V hV hZ D hD0 hD z).toReal : ℂ) *
          W.frozenTorus (rootResidue W.modulus root r) center
            (physicalGridFactorInput W.cover poly (physicalAffineSite root z)) := by
  rw [selectedResidueDensityPMF_complexMean, selectedResidueDensityPMF_complexMean,
    W.selected_weighted_frozenSpatialEval_root_eq center poly root r V hV hZ (fun z => (D z : ℂ))]

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem monomialArrayPolynomial_eval_normalized_input
    {C K : Type*} [Fintype C] (e : C → K →₀ ℕ) (a : C → ℝ)
    (scale x : K → ℝ) (hscale : ∀ k, scale k ≠ 0) :
    MvPolynomial.eval (fun k => x k / scale k)
      (monomialArrayPolynomial e (fun c => a c * monomialScale scale (e c))) =
    MvPolynomial.eval x (monomialArrayPolynomial e a) := by
  have hm (c : C) : monomialScale scale (e c) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k _ => pow_ne_zero _ (hscale k))
  have h := monomialArrayPolynomial_rescale e
    (fun c => a c * monomialScale scale (e c)) scale (fun k => x k / scale k)
    1 one_ne_zero hscale
  simpa only [one_mul, div_one, mul_div_cancel_right₀ _ (hm _),
    mul_div_cancel₀ _ (hscale _)] using h.symm

theorem monomialArrayPolynomial_eval_div_coefficients
    {C K : Type*} [Fintype C] (e : C → K →₀ ℕ) (a : C → ℝ) (x : K → ℝ) (H : ℝ) :
    MvPolynomial.eval x (monomialArrayPolynomial e (fun c => a c / H)) =
      MvPolynomial.eval x (monomialArrayPolynomial e a) / H := by
  simp only [monomialArrayPolynomial_eval, Finset.sum_div, div_mul_eq_mul_div]

namespace VectorPolynomial
open Module
variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
local notation "vars" => LayerSamplerVariables G I n B
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "sides" => allocatedPrincipalSides B U basis S

variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S))

local notation "root" => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y
local notation "physical" => allocatedOriginalSamplePhysicalMixedValue B U basis S sample x y

theorem allocatedSampleNormalizedCoefficients_eval_physical (a : LayerSamplerAxis I n) :
    MvPolynomial.eval (fun k => (root k : ℝ) / layerSamplerBox B U basis S k)
      (monomialArrayPolynomial Subtype.val
        (allocatedSampleNormalizedCoefficients B U basis S sample a)) / R a.1 =
      allocatedFullMixedSiteValue (R := R) U basis physical a := by
  have hscale (k : vars) : layerSamplerBox B U basis S k ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U basis S k)).ne'
  rcases a with ⟨j, i | i⟩
  · have hc : allocatedSampleNormalizedCoefficients B U basis S sample ⟨j, .inl i⟩ =
        fun d => (sample j).1 i d * monomialScale (layerSamplerBox B U basis S) d.val :=
      funext (allocatedSampleNormalizedCoefficients_continuous B U basis S sample j i)
    rw [hc]
    dsimp only [layerSamplerDegree]
    erw [monomialArrayPolynomial_eval_normalized_input _ _ _ _ hscale]
    change _ = (physical j).1 i / R j
    rw [allocatedOriginalSamplePhysicalMixedValue_real]
    rfl
  · have hc : allocatedSampleNormalizedCoefficients B U basis S sample ⟨j, .inr i⟩ =
        fun d => ((sample j).2 i d : ℝ) * monomialScale (layerSamplerBox B U basis S) d.val /
          (basisAxisScale (basis j) i : ℝ) :=
      funext (allocatedSampleNormalizedCoefficients_integer B U basis S sample j i)
    rw [hc]
    dsimp only [layerSamplerDegree]
    erw [monomialArrayPolynomial_eval_div_coefficients,
      monomialArrayPolynomial_eval_normalized_input _ _ _ _ hscale]
    change _ = ((physical j).2 i : ℝ) / basisAxisScale (basis j) i / R j
    rw [allocatedOriginalSamplePhysicalMixedValue_integer_cast]
    rfl

theorem allocatedPrincipalSides_not_short (a : Active)
    (p : B a.val × Fin (layerSamplerDegree I n a.val)) :
    sides ⟨a.val,p⟩ = S.value := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · rfl
  · exact allocatedPrincipalSides_active B U basis S j i (Nat.lt_of_not_ge ha) p.1 p.2

theorem allocatedOriginalSampleSliceInput_physical :
    allocatedOriginalSampleSliceInput B U basis S x (principalAxisRestrict short y)
      (fun _ _ => 0) (fun _ _ => 1)
      (fun j : Input => (y ⟨j.1.val,j.2⟩ none : ℝ) / S.value) =
      fun k => (root k : ℝ) / layerSamplerBox B U basis S k := by
  funext k
  rcases k with g | ⟨a,b,i⟩
  · simp [allocatedOriginalSampleSliceInput, allocatedPhysicalCubeRoot, layerSamplerBox,
      layerSamplerSides, heterogeneousSamplerSides]
  · by_cases ha : short a
    · simp only [allocatedOriginalSampleSliceInput, ha, ↓reduceDIte,
        principalAxisRestrict, allocatedPhysicalCubeRoot, zero_add, Sum.elim_inr]
      rfl
    · simp only [allocatedOriginalSampleSliceInput, ha, ↓reduceDIte,
        zero_add, one_mul, allocatedPhysicalCubeRoot, Sum.elim_inr]
      change _ / (S.value : ℝ) = _ / (sides ⟨a,b,i⟩ : ℝ)
      exact congrArg (fun l : ℕ => (y ⟨a,b,i⟩ none : ℝ) / (l : ℝ))
        (allocatedPrincipalSides_not_short B U basis S ⟨a,ha⟩ (b,i)).symm

theorem allocatedOriginalSampleFullSliceMap_physical :
    allocatedOriginalSampleFullSliceMap B U basis S x (principalAxisRestrict short y)
      (fun _ _ => 0) (fun _ _ => 1) sample
      (fun j : Input => (y ⟨j.1.val,j.2⟩ none : ℝ) / S.value) =
      fun o : Output => allocatedFullMixedSiteValue (R := R) U basis physical o.1.val := by
  funext o
  rw [allocatedOriginalSampleFullSliceMap_eq_eval, allocatedOriginalSampleSliceInput_physical]
  exact allocatedSampleNormalizedCoefficients_eval_physical B U basis S sample x y o.1.val

omit y in
theorem allocatedOriginalSampleFullSliceMap_physical_join
    (u : PrincipalAxisTuples (α := Empty) short sides)
    (v : PrincipalAxisTuples (α := Empty) (fun a => ¬short a) sides) :
    allocatedOriginalSampleFullSliceMap B U basis S x u
      (fun _ _ => 0) (fun _ _ => 1) sample
      (fun j : Input => (v j none : ℝ) / S.value) =
      fun o : Output => allocatedFullMixedSiteValue (R := R) U basis
        (allocatedOriginalSamplePhysicalMixedValue B U basis S sample x
          (principalAxisJoin short u v)) o.1.val := by
  have h := allocatedOriginalSampleFullSliceMap_physical B U basis S sample x
    (principalAxisJoin short u v)
  rw [principalAxisRestrict_join_left] at h
  have hv : (fun j : Input =>
      (principalAxisJoin short u v ⟨j.1.val,j.2⟩ none : ℝ) / S.value) =
      (fun j : Input => (v j none : ℝ) / S.value) := by
    funext j
    simp only [principalAxisJoin, j.1.property, ↓reduceDIte]
  rw [hv] at h
  exact h

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {K : Type*} [Fintype K] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)]
variable [BorelSpace (CoefficientTorus (K := K) U)]
variable (μ : Measure (CoefficientTorus (K := K) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : Unit => ν j))

theorem coefficientOneSiteJet_measurePreserving (root : K → ℤ) :
    MeasurePreserving (euclideanCoefficientJetMap U root (0 : Matrix Empty K ℤ)
      (fun _ (_ : Unit) => ∅)) μ haar := by
  apply euclideanCoefficientJetMap_measurePreserving U root (0 : Matrix Empty K ℤ)
    1 one_ne_zero ?_ (fun _ (_ : Unit) => ∅) ?_ ?_ μ ν
  · intro v hv
    refine ⟨0, ?_⟩
    exact Subsingleton.elim _ _
  · intro j a b hab
    exact Subsingleton.elim _ _
  · intro j a
    simp

theorem coefficientAmbientRoot_haar_integral (root : K → ℤ)
    (f : ((Σ j, J j) → UnitAddCircle) → ℂ) (hf : Measurable f) :
    (∫ x, f (coefficientAmbientRoot root (coefficientAmbientTorus U x)) ∂μ) =
      ∫ y, f (fun a => coveredJetAmbientTorus U 1 y ⟨a.1, (), a.2⟩) ∂haar := by
  let jet := euclideanCoefficientJetMap U root (0 : Matrix Empty K ℤ)
    (fun _ (_ : Unit) => ∅)
  have hp := coefficientOneSiteJet_measurePreserving U μ ν root
  have hm : Measurable (fun y : EuclideanJetLayers U (fun _ => Unit) =>
      f (fun a => coveredJetAmbientTorus U 1 y ⟨a.1, (), a.2⟩)) := by
    apply hf.comp
    apply Measurable.of_eval
    intro a
    exact ((continuous_apply (⟨a.1, (), a.2⟩ : JetAmbientIndex (fun _ : Fin m => Unit) J)).comp
      (coveredJetAmbientTorus_continuous (O := fun _ : Fin m => Unit) U 1)).measurable
  have hm' : AEStronglyMeasurable (fun y : EuclideanJetLayers U (fun _ => Unit) =>
      f (fun a => coveredJetAmbientTorus U 1 y ⟨a.1, (), a.2⟩))
      (Measure.map jet μ) := by
    rw [hp.map_eq]
    exact hm.aestronglyMeasurable
  have he := (integral_map hp.measurable.aemeasurable hm').symm
  rw [hp.map_eq] at he
  simpa only [Function.comp_def, jet, ← coefficientAmbientRoot_eq_oneSiteJet U root] using he

namespace NormalizedPolynomialTwist

variable {X : Type*} [Fintype X] {periodCap coverCap : ℝ} {L : ℝ≥0}

noncomputable def frozenSingleSiteHaarReference
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (residue : X → ZMod W.modulus) (center : X → ℝ) : ℂ :=
  ∫ y, W.frozenTorus residue center
    (fun a => coveredJetAmbientTorus U 1 y ⟨a.1, (), a.2⟩) ∂haar

omit [∀ j, (ν j).IsAddLeftInvariant] in
theorem frozenSingleSiteHaarReference_integrable
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (residue : X → ZMod W.modulus) (center : X → ℝ) :
    Integrable (fun y : EuclideanJetLayers U (fun _ => Unit) =>
      W.frozenTorus residue center
        (fun a => coveredJetAmbientTorus U 1 y ⟨a.1, (), a.2⟩)) haar := by
  have : ∀ j, IsProbabilityMeasure (Measure.pi (fun _ : Unit => ν j)) :=
    fun _ => Measure.pi.instIsProbabilityMeasure _
  have : IsProbabilityMeasure haar := Measure.pi.instIsProbabilityMeasure _
  apply Integrable.of_bound _ 1 (ae_of_all _ (fun _ => W.norm_frozenTorus_le _ _ _))
  apply Continuous.aestronglyMeasurable
  apply (W.frozenTorus_lipschitz residue center).continuous.comp
  apply continuous_pi
  intro a
  exact (continuous_apply (⟨a.1, (), a.2⟩ : JetAmbientIndex (fun _ : Fin m => Unit) J)).comp
    (coveredJetAmbientTorus_continuous (O := fun _ : Fin m => Unit) U 1)

omit [∀ j, (ν j).IsAddLeftInvariant] in
theorem norm_frozenSingleSiteHaarReference_le
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (residue : X → ZMod W.modulus) (center : X → ℝ) :
    ‖W.frozenSingleSiteHaarReference U ν residue center‖ ≤ 1 := by
  have : ∀ j, IsProbabilityMeasure (Measure.pi (fun _ : Unit => ν j)) :=
    fun _ => Measure.pi.instIsProbabilityMeasure _
  have : IsProbabilityMeasure haar := Measure.pi.instIsProbabilityMeasure _
  exact (norm_integral_le_of_norm_le_const (ae_of_all haar
    (fun _ => W.norm_frozenTorus_le residue center _))).trans_eq (by simp)

omit [∀ j, (ν j).IsAddLeftInvariant] in
theorem frozenSingleSiteHaarReference_lipschitz
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (residue : X → ZMod W.modulus) :
    LipschitzWith L (W.frozenSingleSiteHaarReference U ν residue) := by
  have : ∀ j, IsProbabilityMeasure (Measure.pi (fun _ : Unit => ν j)) :=
    fun _ => Measure.pi.instIsProbabilityMeasure _
  have : IsProbabilityMeasure haar := Measure.pi.instIsProbabilityMeasure _
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  exact probability_integral_approximation haar _ _
    (W.frozenSingleSiteHaarReference_integrable U ν residue x)
    (W.frozenSingleSiteHaarReference_integrable U ν residue y)
    (fun z => W.frozenTorus_spatial_error residue x y _)

theorem frozenAmbientRootObservable_integral
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (residue : X → ZMod W.modulus) (center : X → ℝ) (root : K → ℤ) :
    (∫ x, W.frozenAmbientRootObservable residue center root
      (coefficientAmbientTorus U x) ∂μ) =
      W.frozenSingleSiteHaarReference U ν residue center :=
  coefficientAmbientRoot_haar_integral U μ ν root _
    (W.frozenTorus_lipschitz residue center).continuous.measurable

end NormalizedPolynomialTwist

theorem exists_normalizedTwist_singleSite_haar_sampling (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X K : Type*}
    [Fintype X] [DecidableEq X] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {P : ℝ},
    0 ≤ P → (Fintype.card X : ℝ) ≤ P →
    (Fintype.card (Option K × X) : ℝ) ≤ P →
    ∀ (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
    (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)) →
    ∀ (_hm : ∀ j e, coefficients (poly j) e ∈ U j)
    {periodCap coverCap : ℝ} {L : ℝ≥0}
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L),
    (W.cover : ℝ) ≤ Real.exp P → (W.modulus : ℝ) ≤ Real.exp P →
    ∀ {Rrank ρ ε : ℝ}, 0 < ρ → 0 < ε → 1 / ρ ≤ Real.exp P → 1 / ε ≤ Real.exp P →
    ∀ (H : X → ℝ), (∀ k, Real.exp ((P + A) ^ A) ≤ H k) →
    (∀ j, HasLayerSamplingRank (j.val + 1) H Rrank (U j) (poly j)) →
    Real.exp ((P + A) ^ A) ≤ Rrank →
    ∀ (width : Option K × X → ℝ) (hwidth : ∀ z, 0 < width z),
    (∀ z, ρ * H z.2 ≤ width z) →
    ∀ (root : K → ℤ)
    (r : ColumnResiduePattern (Option K) X (fun _ => W.modulus))
    (center : X → ℝ) {η Q : ℝ},
    0 < η → 0 ≤ Q → (Fintype.card (CoefficientAmbientIndex K J) : ℝ) ≤ Q →
    ((L * coefficientAmbientRootLip m root : ℝ≥0) : ℝ) ≤ Real.exp Q →
    η⁻¹ ≤ Real.exp Q → Real.exp ((2 * Q + 2) ^ 4) ≤ Real.exp P →
    Real.exp (2 * Q * (2 * Q + 2) ^ 4) ≤ Real.exp P →
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ => W.modulus) {r} width z,
      ‖(∑' z : Option K × X → ℤ,
        ((selectedResidueSmoothPMF (fun _ => W.modulus) {r} width hwidth hZ z).toReal : ℂ) *
          W.frozenSpatialEval center poly (integerPhysicalSite root z)) -
        W.frozenSingleSiteHaarReference U ν
          (NormalizedPolynomialTwist.rootResidue W.modulus root r) center‖ ≤ 2 * η + ε := by
  obtain ⟨A, hA, hs⟩ := exists_coefficient_ambient_cover_sampling m
  refine ⟨A, hA, ?_⟩
  intro X K _ _ _ J _ P hP hX hframe U _ _ _ μ _ _ ν _ _ poly hp hm
    periodCap coverCap L W hcover hmodulus Rrank ρ ε hρ hε hρP hεP
    H hsize hrank hR width hwidth hwide root r center η Q hη hQ hdim hLQ hηQ hfreq hmass
  let residue := NormalizedPolynomialTwist.rootResidue W.modulus root r
  obtain ⟨hZ, hcomp⟩ := hs hP hX hframe U μ poly hp hm W.cover W.cover_pos hcover
    (fun _ => W.modulus) (fun _ => W.modulus_pos) (Nat.cast_nonneg W.modulus) hmodulus
    hρ hε hρP hεP (fun _ => le_rfl) H hsize hrank hR {r} (Finset.singleton_nonempty r)
    width hwidth hwide (W.frozenAmbientRootObservable residue center root)
    (L * coefficientAmbientRootLip m root) 1
    (W.frozenAmbientRootObservable_lipschitz residue center root)
    (W.norm_frozenAmbientRootObservable_le residue center root)
    hη hQ hdim hLQ hηQ hfreq (by simpa only [NNReal.coe_one, mul_one] using hmass)
  refine ⟨hZ, ?_⟩
  rw [W.frozenAmbientRootObservable_integral U μ ν residue center root] at hcomp
  simp_rw [W.frozenAmbientRootObservable_sample residue center root U poly hp hm] at hcomp
  rw [W.selected_frozenSpatialEval_root_eq center poly root r width hwidth hZ]
  exact hcomp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped Classical NNReal

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

noncomputable def singleSiteIntegerCover (d : ℕ) :
    EuclideanJetLayers U (fun _ => Unit) →+ EuclideanJetLayers U (fun _ => Unit) where
  toFun y j t := quotientIntegerCover _ d (y j t)
  map_zero' := by ext j t; exact map_zero _
  map_add' x y := by ext j t; exact map_add _ _ _

theorem singleSiteIntegerCover_continuous (d : ℕ) :
    Continuous (singleSiteIntegerCover U d) := by
  apply continuous_pi
  intro j
  apply continuous_pi
  intro t
  exact (quotientIntegerCover_continuous _ d).comp
    ((continuous_apply t).comp (continuous_apply j))

theorem singleSiteIntegerCover_surjective (d : ℕ) (hd : 0 < d) :
    Function.Surjective (singleSiteIntegerCover U d) := by
  intro y
  choose x hx using fun j t => quotientIntegerCover_surjective
    (latticeSection (standardEuclideanLattice (J j))
      (euclideanSubspace (U j))).toAddSubgroup d hd (y j t)
  exact ⟨x, funext fun j => funext fun t => hx j t⟩

theorem coveredJetAmbientTorus_singleSiteIntegerCover (d : ℕ)
    (y : EuclideanJetLayers U (fun _ => Unit)) :
    coveredJetAmbientTorus U 1 (singleSiteIntegerCover U d y) =
      coveredJetAmbientTorus U d y := by
  ext a
  simp only [coveredJetAmbientTorus, singleSiteIntegerCover, AddMonoidHom.coe_mk,
    quotientIntegerCover, nsmulAddMonoidHom_apply, one_nsmul]
  rfl

theorem physicalSingleSiteValue_product_projection
    {X : Type*} (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (a d : ℕ) (ha : 0 < a) (u : X → ℝ) :
    singleSiteIntegerCover U a (physicalSingleSiteValue U (a * d) poly hm u) =
      physicalSingleSiteValue U d poly hm u := by
  have ha0 : (a : ℝ) ≠ 0 := (Nat.cast_pos.mpr ha).ne'
  ext j t
  cases t
  change quotientIntegerCover _ a (physicalSingleSiteValue U (a * d) poly hm u j ()) = _
  rw [physicalSingleSiteValue_eq_mk, physicalSingleSiteValue_eq_mk]
  change quotientIntegerCover _ a (QuotientAddGroup.mk' _ _) = QuotientAddGroup.mk' _ _
  rw [quotientIntegerCover_mk, smul_smul, Nat.cast_mul, mul_inv_rev]
  congr 1
  congr 1
  calc
    (a : ℝ) * ((d : ℝ)⁻¹ * (a : ℝ)⁻¹) =
        (d : ℝ)⁻¹ * ((a : ℝ) * (a : ℝ)⁻¹) := by ring
    _ = (d : ℝ)⁻¹ := by rw [mul_inv_cancel₀ ha0, mul_one]

theorem physicalSingleSiteValue_divisor_projection
    {X : Type*} (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (Q d : ℕ) (hQ : 0 < Q) (hd : d ∣ Q) (u : X → ℝ) :
    singleSiteIntegerCover U (Q / d) (physicalSingleSiteValue U Q poly hm u) =
      physicalSingleSiteValue U d poly hm u := by
  have hdpos := Nat.pos_of_dvd_of_pos hd hQ
  have ha : 0 < Q / d := Nat.div_pos (Nat.le_of_dvd hQ hd) hdpos
  simpa only [Nat.div_mul_cancel hd] using
    physicalSingleSiteValue_product_projection U poly hm (Q / d) d ha u

theorem physicalSingleSiteValue_gridFactorInput
    {X : Type*} (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (d : ℕ) (u : X → ℝ) :
    (fun a : Σ j, J j => coveredJetAmbientTorus U 1
      (physicalSingleSiteValue U d poly hm u) ⟨a.1, (), a.2⟩) =
      physicalGridFactorInput d poly u := by
  funext a
  change subspaceAmbientTorus (U a.1) (euclideanSubspaceTorusEquiv (U a.1)
    (1 • (euclideanSubspaceTorusEquiv (U a.1)).symm
      (QuotientAddGroup.mk' (subspaceArrayIntegerLattice Unit (U a.1))
        (fun _ => (d : ℝ)⁻¹ • eval u
          (restrictCoefficients (U a.1) (poly a.1) (hm a.1)))))) a.2 = _
  rw [one_nsmul, AddEquiv.apply_symm_apply, subspaceAmbientTorus_mk]
  simp only [Pi.smul_apply, Submodule.coe_smul, smul_eq_mul, eval_restrictCoefficients,
    physicalGridFactorInput, div_eq_mul_inv, mul_comm]

theorem physicalSingleSiteValue_commonCover_gridFactorInput
    {X : Type*} (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (Q d : ℕ) (hQ : 0 < Q) (hd : d ∣ Q) (u : X → ℝ) :
    (fun a : Σ j, J j => coveredJetAmbientTorus U (Q / d)
      (physicalSingleSiteValue U Q poly hm u) ⟨a.1, (), a.2⟩) =
      physicalGridFactorInput d poly u := by
  rw [← coveredJetAmbientTorus_singleSiteIntegerCover,
    physicalSingleSiteValue_divisor_projection U poly hm Q d hQ hd]
  exact physicalSingleSiteValue_gridFactorInput U poly hm d u

theorem singleSite_compactSpace_of_coefficientTorus {K : Type*} [Fintype K]
    [CompactSpace (CoefficientTorus (K := K) U)] :
    CompactSpace (EuclideanJetLayers U (fun _ => Unit)) := by
  let root : K → ℤ := 0
  let rows : ∀ _ : Fin m, Unit → Finset Empty := fun _ _ => ∅
  have hc := euclideanCoefficientJetMap_continuous U root (0 : Matrix Empty K ℤ) rows
  have hs : Function.Surjective (euclideanCoefficientJetMap U root (0 : Matrix Empty K ℤ) rows) := by
    apply euclideanCoefficientJetMap_surjective U root (0 : Matrix Empty K ℤ)
      1 one_ne_zero ?_ rows ?_ ?_
    · intro v hv
      exact ⟨0, Subsingleton.elim _ _⟩
    · intro j a b hab
      exact Subsingleton.elim _ _
    · intro j a
      simp [rows]
  have h := isCompact_univ.image hc
  rw [Set.image_univ, Set.range_eq_univ.mpr hs] at h
  exact ⟨h⟩

variable [CompactSpace (EuclideanJetLayers U (fun _ => Unit))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : Unit => ν j))

theorem singleSiteIntegerCover_measurePreserving (d : ℕ) (hd : 0 < d) :
    MeasurePreserving (singleSiteIntegerCover U d) haar haar := by
  let : ∀ j, MeasurableAdd (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j))
        (euclideanSubspace (U j))).toAddSubgroup) := fun _ => inferInstance
  let : ∀ j, MeasurableAdd (Unit → euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j))
        (euclideanSubspace (U j))).toAddSubgroup) := fun _ => inferInstance
  let : ∀ j, IsProbabilityMeasure (Measure.pi (fun _ : Unit => ν j)) :=
    fun _ => Measure.pi.instIsProbabilityMeasure _
  let : IsProbabilityMeasure haar := Measure.pi.instIsProbabilityMeasure _
  let : ∀ j, (Measure.pi (fun _ : Unit => ν j)).IsAddLeftInvariant :=
    fun _ => Measure.pi.isAddLeftInvariant _
  let : Measure.IsAddLeftInvariant haar := Measure.pi.isAddLeftInvariant _
  let : Measure.IsAddHaarMeasure haar :=
    { toIsFiniteMeasureOnCompacts := ⟨fun s _ =>
        (measure_mono (Set.subset_univ s)).trans_lt (by simp)⟩
      toIsAddLeftInvariant := inferInstance
      toIsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_compact
        (μ := haar) Set.univ isCompact_univ (by simp) }
  exact AddMonoidHom.measurePreserving (singleSiteIntegerCover_continuous U d)
    (singleSiteIntegerCover_surjective U d hd) rfl

theorem singleSiteIntegerCover_integral (d : ℕ) (hd : 0 < d)
    (f : EuclideanJetLayers U (fun _ => Unit) → ℂ)
    (hf : AEStronglyMeasurable f haar) :
    (∫ y, f (singleSiteIntegerCover U d y) ∂haar) = ∫ y, f y ∂haar := by
  have hp := singleSiteIntegerCover_measurePreserving U ν d hd
  have hf' : AEStronglyMeasurable f (Measure.map (singleSiteIntegerCover U d) haar) := by
    rwa [hp.map_eq]
  simpa only [hp.map_eq] using (integral_map hp.measurable.aemeasurable hf').symm

namespace NormalizedPolynomialTwist

variable {X : Type*} [Fintype X] {periodCap coverCap : ℝ} {L : ℝ≥0}

theorem frozenSingleSiteHaarReference_commonCover
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (residue : X → ZMod W.modulus) (center : X → ℝ)
    (Q : ℕ) (hQ : 0 < Q) (hcover : W.cover ∣ Q) :
    (∫ y, W.frozenTorus residue center
      (fun a => coveredJetAmbientTorus U (Q / W.cover) y ⟨a.1, (), a.2⟩) ∂haar) =
      W.frozenSingleSiteHaarReference U ν residue center := by
  have hd : 0 < Q / W.cover := Nat.div_pos (Nat.le_of_dvd hQ hcover) W.cover_pos
  have h := singleSiteIntegerCover_integral U ν (Q / W.cover) hd
    (fun y => W.frozenTorus residue center
      (fun a => coveredJetAmbientTorus U 1 y ⟨a.1, (), a.2⟩))
    (W.frozenSingleSiteHaarReference_integrable U ν residue center).aestronglyMeasurable
  simpa only [coveredJetAmbientTorus_singleSiteIntegerCover, frozenSingleSiteHaarReference]
    using h

end NormalizedPolynomialTwist
end Erdos3.VectorPolynomial

end

end OAI
