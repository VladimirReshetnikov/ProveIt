import OAI.Combinatorics.Progressions.Lattices.AllocatedResidueSitePrimitiveAverage

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem complexMean_fiber_reconstruction_error
    {Ω R V Y : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype R] [DecidableEq R]
    (p : FiniteProbabilityWeights Ω) (label : Ω → R)
    (window : R → Finset V) (reconstruct : R → V → Y)
    (weight : R → V → ℂ) (source : Ω → Y → ℂ) (target : R → Y → ℂ)
    (error : R → ℝ)
    (he : ∀ r (hr : 0 < p.mass (Finset.univ.filter (fun x => label x = r))),
      (∑ v ∈ window r, ‖weight r v‖ *
        ‖(p.condition _ hr).complexMean (fun x => source x (reconstruct r v)) -
          target r (reconstruct r v)‖) ≤ error r) :
    ‖p.complexMean (fun x => ∑ v ∈ window (label x),
        weight (label x) v * source x (reconstruct (label x) v)) -
      (p.fiberLaw label).complexMean (fun r => ∑ v ∈ window r,
        weight r v * target r (reconstruct r v))‖ ≤ (p.fiberLaw label).mean error := by
  apply p.complexMean_supported_fiber_variable_error label
  intro r hr
  let c := p.condition (Finset.univ.filter (fun x => label x = r)) hr
  have hfreeze : c.complexMean (fun x => ∑ v ∈ window (label x),
      weight (label x) v * source x (reconstruct (label x) v)) =
      c.complexMean (fun x => ∑ v ∈ window r,
        weight r v * source x (reconstruct r v)) := by
    apply c.complexMean_congr_support
    intro x hx
    have hl : label x = r := (Finset.mem_filter.mp (condition_weight_support p _ hr x hx).1).2
    rw [hl]
  change ‖c.complexMean _ - _‖ ≤ _
  rw [hfreeze, c.complexMean_finset_sum]
  simp_rw [c.complexMean_mul_left]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  apply (norm_sum_le _ _).trans
  simpa only [norm_mul] using he r hr

end Erdos3.FiniteProbabilityWeights

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem physicalReconstruction_fiber_error
    {Ω R X K : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype R] [DecidableEq R]
    [Fintype X] [Fintype K] {dim : ℕ}
    (p : FiniteProbabilityWeights Ω) (label : Ω → R)
    (stride : X → ℕ) (hs : ∀ x, 0 < stride x)
    (root : R → K → ℤ) (D : R → Matrix (Fin dim) K ℤ) (base : R → X → ℤ)
    (residue : R → ColumnResiduePattern (Option K) X stride)
    (H : X → ℝ) (hH : ∀ x, 0 < H x)
    (hrows : ∀ r x i, (∑ k, |(physicalCubeCoefficient (root r) (D r) i k : ℝ)|) ≤ H x)
    (hscale : ∀ x, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H x)
    (source : Ω → (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)
    (target : R → (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)
    (weight : R → (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)
    {C : ℝ} (hC : 0 ≤ C)
    (hw : ∀ r v, v ∈ spatialWindow H 4 → ‖weight r v‖ ≤ C)
    (ε : R → ℝ)
    (he : ∀ r (hr : 0 < p.mass (Finset.univ.filter (fun x => label x = r))),
      let a := boundedColumnResidueRepresentative stride (residue r)
      let cell := columnResiduePattern stride
        (standardPhysicalCubeFrame (physicalCubeRootDifferences (root r) (D r) 0 a))
      let V := referenceJetEnvelopeWidths (q := dim) stride H
      (0 < ∑' z, selectedResidueSmoothWeight stride {cell} V z) ∧
      selectedResidueDensityMass stride {cell} V (fun z =>
        ‖(p.condition _ hr).complexMean (fun x =>
            source x (translatePhysicalCube (base r) (standardPhysicalCubeOutput z))) -
          target r (translatePhysicalCube (base r) (standardPhysicalCubeOutput z))‖) ≤ ε r) :
    let reconstruct := fun r => physicalResidueReconstruction (root r) (D r) (base r)
      (boundedColumnResidueRepresentative stride (residue r)) stride
    let factor := (3 / 2 : ℝ) ^ Fintype.card (Option (Fin dim) × X) *
      (∏ i, residueProfileWidth stride (referenceJetEnvelopeWidths (q := dim) stride H) i) /
      (smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X)
    ‖p.complexMean (fun x => ∑ v ∈ spatialWindow H 4,
        weight (label x) v * source x (reconstruct (label x) v)) -
      (p.fiberLaw label).complexMean (fun r => ∑ v ∈ spatialWindow H 4,
        weight r v * target r (reconstruct r v))‖ ≤
      C * factor * (p.fiberLaw label).mean ε := by
  intro reconstruct factor
  have hfactor : 0 ≤ factor := by
    apply div_nonneg
    · exact mul_nonneg (pow_nonneg (by norm_num) _)
        (Finset.prod_nonneg (fun i _ => (residueProfileWidth_pos stride _ hs
          (referenceJetEnvelopeWidths_pos stride hs H hH) i).le))
    · exact (pow_pos smoothProbabilityProfile_pos_zero _).le
  have hlocal (r) (hr : 0 < p.mass (Finset.univ.filter (fun x => label x = r))) :
      (∑ v ∈ spatialWindow H 4, ‖weight r v‖ *
        ‖(p.condition _ hr).complexMean (fun x => source x (reconstruct r v)) -
          target r (reconstruct r v)‖) ≤ C * factor * ε r := by
    let f := fun v => ‖(p.condition _ hr).complexMean (fun x =>
      source x (translatePhysicalCube (base r) v)) - target r (translatePhysicalCube (base r) v)‖
    have h := physicalReconstruction_sum_le_sampled_mass stride hs (root r) (D r)
      (residue r) H hH (hrows r) hscale f (fun _ => norm_nonneg _) (he r hr).1
    have hrec (v) : reconstruct r v = translatePhysicalCube (base r)
        (physicalResidueReconstruction (root r) (D r) 0
          (boundedColumnResidueRepresentative stride (residue r)) stride v) :=
      physicalResidueReconstruction_translate _ _ _ _ _ _
    have hsum : (∑ v ∈ spatialWindow H 4,
        ‖(p.condition _ hr).complexMean (fun x => source x (reconstruct r v)) -
          target r (reconstruct r v)‖) ≤ factor * ε r := by
      simp only [hrec]
      exact h.trans (mul_le_mul_of_nonneg_left (he r hr).2 hfactor)
    calc
      _ ≤ ∑ v ∈ spatialWindow H 4, C *
          ‖(p.condition _ hr).complexMean (fun x => source x (reconstruct r v)) -
            target r (reconstruct r v)‖ := by
        exact Finset.sum_le_sum (fun v hv => mul_le_mul_of_nonneg_right (hw r v hv) (norm_nonneg _))
      _ = C * ∑ v ∈ spatialWindow H 4,
          ‖(p.condition _ hr).complexMean (fun x => source x (reconstruct r v)) -
            target r (reconstruct r v)‖ := (Finset.mul_sum _ _ _).symm
      _ ≤ C * (factor * ε r) := mul_le_mul_of_nonneg_left hsum hC
      _ = _ := (mul_assoc _ _ _).symm
  have h := p.complexMean_fiber_reconstruction_error label (fun _ => spatialWindow H 4)
    reconstruct weight source target (fun r => C * factor * ε r) hlocal
  simpa only [FiniteProbabilityWeights.mean_const_mul] using h

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

theorem allocatedLongProfileDensity_eq_of_periods
    (u : PrincipalAxisTuples (α := α) grid sides)
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (M N : ℕ)
    (r : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod M))
    (s : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod N))
    (hM : ∀ j, integerScalarLattice (O j) (M : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hN : ∀ j, integerScalarLattice (O j) (N : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hr : ∀ j, integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) M = r j)
    (hs : ∀ j, integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) N = s j)
    (f : (output → ℝ) → ℝ) :
    allocatedLongProfileDensity B U b S x rows M r f =
      allocatedLongProfileDensity B U b S x rows N s f := by
  funext z
  unfold allocatedLongProfileDensity
  have hmask : (∏ a, allocatedLongJetMask B U b S x rows M r a (z a)) =
      ∏ a, allocatedLongJetMask B U b S x rows N s a (z a) :=
    Finset.prod_congr rfl (fun a _ => allocatedLongJetMask_eq_of_periods
      B U b S x rows u v M N r s hM hN hr hs a (z a))
  rw [hmask]

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

theorem allocatedWholeMaskedGridlessProfile_eq_of_periods
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α sides)
    (M N : ℕ)
    (hM : ∀ j, integerScalarLattice (O j) (M : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hN : ∀ j, integerScalarLattice (O j) (N : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (f : (output → ℝ) → ℝ) :
    allocatedWholeMaskedGridlessProfile B U b S x y rows hb o bW d M f =
      allocatedWholeMaskedGridlessProfile B U b S x y rows hb o bW d N f := by
  unfold allocatedWholeMaskedGridlessProfile
  rw [allocatedLongProfileDensity_eq_of_periods B U b S x rows
    (principalAxisRestrict grid y) (principalAxisRestrict (fun a => ¬grid a) y)
    M N _ _ hM hN (fun _ => rfl) (fun _ => rfl)]

theorem allocatedWholeMaskedCoveredProfile_eq_of_periods [Fintype α]
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α sides)
    (M N : ℕ)
    (hM : ∀ j, integerScalarLattice (O j) (M : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hN : ∀ j, integerScalarLattice (O j) (N : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (f : (output → ℝ) → ℝ) :
    allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y M f =
      allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y N f := by
  unfold allocatedWholeMaskedCoveredProfile
  rw [allocatedLongProfileDensity_eq_of_periods B U b S x rows
    (principalAxisRestrict grid y) (principalAxisRestrict (fun a => ¬grid a) y)
    M N _ _ hM hN (fun _ => rfl) (fun _ => rfl)]

theorem allocatedWholeMaskedCoveredProfile_refine [Fintype α]
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α sides)
    (M N : ℕ) (hdiv : M ∣ N)
    (hM : ∀ j, integerScalarLattice (O j) (M : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (f : (output → ℝ) → ℝ) :
    allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y M f =
      allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y N f :=
  allocatedWholeMaskedCoveredProfile_eq_of_periods B U b S x rows hR hσ hb o bW d y M N hM
    (fun j => (integerScalarLattice_nat_refinement (O j) hdiv).trans (hM j)) f

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "tuples" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  sides (allocatedPrincipalSides_pos B U b S)
local notation "tupleType" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides
local notation "vars" => LayerSamplerVariables G I n B

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (modulus refined : ℕ) (hdiv : modulus ∣ refined)
variable (hperiod : ∀ j : Fin m,
  integerScalarLattice {s : Finset (Fin dim) // s ∈ boundedBooleanJetRows (Fin dim) (j.val + 1)}
    (modulus : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1)
    (Subtype.val : {s : Finset (Fin dim) // s ∈ boundedBooleanJetRows (Fin dim) (j.val + 1)} →
      Finset (Fin dim))).mulVecLin.range)
variable (f : ((Σ a : {a : LayerSamplerAxis I n // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset (Fin dim) // t ∈ boundedBooleanJetRows (Fin dim) ((Sigma.fst (Subtype.val a)).val + 1)}) → ℝ) → ℝ)
variable (witnesses : (r : AllocatedPositiveResidue (dim := dim) B U b S refined) →
  AllocatedResidueSiteWitness (dim := dim) B U b S refined r.val)

local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)
local notation "target" => allocatedSupportedResidueSiteProfile B U b hR hσ S refined x hb o bW d f witnesses
local notation "conditionalError" r => allocatedSelectedConditionalError (O := rowTypes)
  B U b hR hσ S x (rows) hb o bW d refined
  (AllocatedResidueSiteWitness.representative (witnesses r))
  (AllocatedResidueSiteWitness.positive (witnesses r))
  (allocatedActiveGrid B U b S) f
  (allocatedActiveSiteApproximation B U b S rowSets (AllocatedResidueSiteWitness.expansion (witnesses r)))
  (allocatedActiveNaturalVolume B U b S rowSets)

include hdiv hperiod f

theorem allocatedSupportedResidueSiteProfile_refined_error
    (r : AllocatedPositiveResidue (dim := dim) B U b S refined) :
    (fun z => ((tuples).condition _ r.property).complexMean (fun y =>
      (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x (rows)
        hb o bW d y modulus f z : ℂ)) - target r.val z) = conditionalError r := by
  simp_rw [allocatedWholeMaskedCoveredProfile_refine B U b S x (rows)
    hR hσ hb o bW d _ modulus refined hdiv hperiod f]
  exact allocatedSupportedResidueSiteProfile_error B U b hR hσ S refined x hb o bW d f witnesses r

variable [NeZero refined]

theorem allocatedRefinedCover_reconstruction_error
    {X : Type*} [Fintype X]
    (reference : labels → tupleType)
    (stride : X → ℕ) (hs : ∀ t, 0 < stride t) (base : X → ℤ)
    (residue : labels → ColumnResiduePattern (Option vars) X stride)
    (H : X → ℝ) (hH : ∀ t, 0 < H t)
    (hrows : ∀ t, Fintype.card (Option vars) * allocatedPhysicalEntryBudget B U b S (fun _ => 0) ≤ H t)
    (hscale : ∀ t, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H t)
    (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U rowTypes)
    (weight : labels → (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)
    {C : ℝ} (hC : 0 ≤ C) (hw : ∀ r v, v ∈ spatialWindow H 4 → ‖weight r v‖ ≤ C)
    (ε : labels → ℝ)
    (hsampled : ∀ r : AllocatedPositiveResidue (dim := dim) B U b S refined,
      let root := allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (reference r.val)
      let dirs := allocatedPhysicalCubeDirections B U b S x (reference r.val)
      let a := boundedColumnResidueRepresentative stride (residue r.val)
      let cell := columnResiduePattern stride
        (standardPhysicalCubeFrame (physicalCubeRootDifferences root dirs 0 a))
      let V := referenceJetEnvelopeWidths (q := dim) stride H
      (0 < ∑' z, selectedResidueSmoothWeight stride {cell} V z) ∧
      selectedResidueDensityMass stride {cell} V (fun z =>
        ‖(conditionalError r) (point (translatePhysicalCube base (standardPhysicalCubeOutput z)))‖) ≤ ε r.val) :
    let reconstruct := fun r => physicalResidueReconstruction
      (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (reference r))
      (allocatedPhysicalCubeDirections B U b S x (reference r)) base
      (boundedColumnResidueRepresentative stride (residue r)) stride
    let factor := (3 / 2 : ℝ) ^ Fintype.card (Option (Fin dim) × X) *
      (∏ i, residueProfileWidth stride (referenceJetEnvelopeWidths (q := dim) stride H) i) /
      (smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X)
    ‖(tuples).complexMean (fun y => ∑ v ∈ spatialWindow H 4,
        weight (principalResidueLabel refined y) v *
          (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x (rows)
            hb o bW d y modulus f (point (reconstruct (principalResidueLabel refined y) v)) : ℂ)) -
      ((tuples).fiberLaw (principalResidueLabel refined)).complexMean (fun r =>
        ∑ v ∈ spatialWindow H 4, weight r v * target r (point (reconstruct r v)))‖ ≤
      C * factor * ((tuples).fiberLaw (principalResidueLabel refined)).mean ε := by
  intro reconstruct factor
  apply physicalReconstruction_fiber_error (tuples) (principalResidueLabel refined) stride hs
    (fun r => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (reference r))
    (fun r => allocatedPhysicalCubeDirections B U b S x (reference r)) (fun _ => base)
    residue H hH (fun r t i =>
      (allocatedPhysicalCube_coefficient_row_sum B U b S (fun _ => 0) x (reference r) i).trans (hrows t))
    hscale
    (fun y v => (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x (rows)
      hb o bW d y modulus f (point v) : ℂ))
    (fun r v => target r (point v)) weight hC hw ε
  intro r hr
  let rr : AllocatedPositiveResidue (dim := dim) B U b S refined := ⟨r, hr⟩
  refine ⟨(hsampled rr).1, ?_⟩
  have he := allocatedSupportedResidueSiteProfile_refined_error B U b hR hσ S x
    hb o bW d modulus refined hdiv hperiod f witnesses rr
  refine (le_of_eq ?_).trans (hsampled rr).2
  apply congrArg (selectedResidueDensityMass stride _ _)
  funext z
  exact congrArg norm (congrFun he (point (translatePhysicalCube base (standardPhysicalCubeOutput z))))

end Erdos3.VectorPolynomial

end

end OAI
