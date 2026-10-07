/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Lattices.AllocatedResidueLabelCount
import OAI.Combinatorics.Progressions.Linear.AllocatedErrorAmbientKernel

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

theorem allocatedLongJetOutputScale_one_le
    (a : {a // ¬allocatedGridAxis (I := I) U b S.value a}) :
    1 ≤ allocatedLongJetOutputScale B U b S (O := O) a := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact le_rfl
  · apply one_le_pow₀
    exact_mod_cast Nat.succ_le_of_lt (basisAxisScale_pos (b j) i)

noncomputable def coefficientErrorCap (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
    (period : ℕ) : ℝ := coefficientDeckPeriodCap O Q period / coveredJetArrayScale (O := O) U

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

theorem coefficientErrorCap_nonneg (Q : Fin m → Type*) [∀ j, Fintype (Q j)] (period : ℕ) :
    0 ≤ coefficientErrorCap (O := O) U Q period :=
  div_nonneg (coefficientDeckPeriodCap_nonneg O Q period) (coveredJetArrayScale_pos U).le

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S))
variable (rows : ∀ j, O j → Finset α)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)] (d period : ℕ) [NeZero d] [NeZero period]
variable (hperiod : ∀ j, integerScalarLattice (O j) (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)

include hperiod

theorem allocatedCoveredFixedFactor_bound
    (z : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ))
    (r : ∀ j, O j → Q j → ZMod d) :
    allocatedCoveredFixedFactor B U b hR hσ S x u v rows Q d z r ≤
      coefficientErrorCap (O := O) U Q period := by
  have hp (j : Fin m) : integerScalarLattice (O j) (period : ℤ) ≤
      (boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x
        (principalAxisJoin (allocatedGridAxis (I := I) U b S.value) u v))
        (allocatedPhysicalCubeDirections B U b S x
          (principalAxisJoin (allocatedGridAxis (I := I) U b S.value) u v))
        (j.val + 1) (rows j)).mulVecLin.range := by
    rw [← allocatedPartitionedJetMatrix_eq_physical B U b S x u v rows j]
    exact (hperiod j).trans (allocatedPartitionedJetMatrix_kernel_range_le B U b S x u v rows j)
  have hd := coefficientDeckJetDensity_period_bound _ _ rows d period hp r
  unfold allocatedCoveredFixedFactor coefficientErrorCap
  apply div_le_div_of_nonneg_right _ (coveredJetArrayScale_pos U).le
  calc
    _ ≤ coefficientDeckJetDensity _ _ rows d r := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (allocatedGridJetDensity_mem_Icc B U b hR hσ S x u v rows _).2
        (coefficientDeckJetDensity_nonneg _ _ rows d r)
    _ ≤ _ := hd

theorem allocatedRestrictedCoefficientError_bound
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    {η : ℝ} (hη : 0 ≤ η) (y : EuclideanJetLayers U O) :
    restrictedChartDensity (mixedCoveredJetChart U o b hb bW d)
      (mixedCoveredJetRegion (O := O) (E := Q) U o b d (fun j _ => standardLatticeClosedQuarterBox (J j)))
      1 (fun z : MixedCoveredJetSource I O Q n d =>
        allocatedCoveredFixedFactor B U b hR hσ S x u v rows Q d z.1 z.2 *
          (η / (∏ a, allocatedLongJetOutputScale B U b S (O := O) a))) y ≤
      η * coefficientErrorCap (O := O) U Q period := by
  have hscale : 1 ≤ ∏ a, allocatedLongJetOutputScale B U b S (O := O) a :=
    Finset.one_le_prod₀ (fun a _ => allocatedLongJetOutputScale_one_le B U b S a)
  have hscale0 : 0 < ∏ a, allocatedLongJetOutputScale B U b S (O := O) a :=
    lt_of_lt_of_le zero_lt_one hscale
  have hfrac : η / (∏ a, allocatedLongJetOutputScale B U b S (O := O) a) ≤ η :=
    (div_le_iff₀ hscale0).mpr (by nlinarith)
  apply restrictedChartDensity_bound _ _
    (mixedCoveredJetChart_injOn U o b hb bW d _
      (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))) _
    (mul_nonneg hη (coefficientErrorCap_nonneg U Q period)) _ y
  intro z _
  have h := mul_le_mul
    (allocatedCoveredFixedFactor_bound B U b S hR hσ x u v rows Q d period hperiod z.1 z.2)
    hfrac (div_nonneg hη hscale0.le) (coefficientErrorCap_nonneg U Q period)
  simpa only [mul_comm] using h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical Matrix

noncomputable def coefficientTailSpatialFactor {α G : Type*} [Fintype α] [Fintype G]
    (X : Type*) [Fintype X] (selection : α ↪ G) (M period : ℕ) (W L : ℝ) : ℝ :=
  ((period : ℝ) ^ Fintype.card (Unit ⊕ α) * anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^
      Fintype.card X *
    (9 ^ Fintype.card (X × (Unit ⊕ α)) * (((1 + W) / L) ^ Fintype.card α) ^ Fintype.card X)

theorem coefficientTailSpatialFactor_bound {α G : Type*} [Fintype α] [Fintype G]
    (X : Type*) [Fintype X] (selection : α ↪ G) (M period : ℕ)
    {W L D : ℝ} (hW : 0 ≤ W) (hL : 1 ≤ L) (hWL : W ≤ D * L) :
    coefficientTailSpatialFactor X selection M period W L ≤
      coefficientTailSpatialFactor X selection M period D 1 := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hratio : (1 + W) / L ≤ 1 + D := (div_le_iff₀ hL0).mpr (by nlinarith)
  have hC := anisotropicSpatialDensityCap_nonneg selection (by positivity : 0 ≤ 1 / (M : ℝ))
  unfold coefficientTailSpatialFactor
  simp only [div_one]
  gcongr

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (rows : ∀ j, O j → Finset α)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

theorem allocatedReferenceCoefficientTail_bound
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d period : ℕ) [NeZero d] [NeZero period]
    (hperiod : ∀ j, integerScalarLattice (O j) (period : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    {M : ℕ} (hM : 0 < M) (selection : α ↪ G)
    (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
    (hspatial : integerScalarLattice (Unit ⊕ α) (period : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
    {X : Type*} [Fintype X] (H T : X → ℝ) (hH : ∀ t, 1 ≤ H t) (hT : ∀ t, 0 < T t)
    {W : ℝ} (hW : 0 ≤ W) (hscale : ∀ t, H t = (1 + W) * T t)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (stride : X → ℕ) (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (V : Option (LayerSamplerVariables G I n B) × X → ℝ) (hV : ∀ z, 0 < V z)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
    (point : (X → (Unit ⊕ α) → ℤ) → EuclideanJetLayers U O)
    (test : (X → (Unit ⊕ α) → ℤ) → ℂ) (htest : ∀ w, ‖test w‖ ≤ 1)
    {η mesh : ℝ} (hη : 0 ≤ η) (hmesh : 0 < mesh) :
    let y₀ := principalAxisJoin (allocatedGridAxis (I := I) U b S.value) u v₀
    let ker := fun g => (0 : ℤ) + (x g none : ℤ)
    let hp := goodScalarKernelTuple_spatial_det_ne_zero selection x ker
      (one_div_pos.mpr (Nat.cast_pos.mpr hM)) hx
    let f := canonicalSpatialSiteDensity selection ker (scalarCubeDifferenceMatrix x) hp W S.value
      hW (Nat.cast_pos.mpr S.positive)
    let ψ := fun w : X → (Unit ⊕ α) → ℤ => ∏ t,
      spatialSiteApprox (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
        (Matrix.fromCols (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection)
          (liftResidueMatrix (integerResidueMatrix (principalSpatialColumns (fun _ => (0 : ℤ)) id y₀) period)))
        period f (H t) 4 mesh (w t)
    let A := ∏ t, ∏ i, physicalSpatialOutputScale α (H t) (T t) S.value i
    let window := spatialWindow H 4
    let F := fun a : cells => physicalResidueReconstruction (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y₀)
      (allocatedPhysicalCubeDirections B U b S x y₀) base (boundedColumnResidueRepresentative stride a.val) stride
    let error := restrictedChartDensity (mixedCoveredJetChart U o b hb bW d)
      (mixedCoveredJetRegion (O := O) (E := Q) U o b d (fun j _ => standardLatticeClosedQuarterBox (J j)))
      1 (fun z : MixedCoveredJetSource I O Q n d =>
        allocatedCoveredFixedFactor B U b hR hσ S x u v₀ rows Q d z.1 z.2 *
          (η / (∏ a, allocatedLongJetOutputScale B U b S (O := O) a)))
    (∑ t : cells × window,
      ‖(selectedResidueCellWeight stride cells V t.1 : ℂ) * (ψ t.2.val / (A : ℂ)) *
        test (F t.1 t.2.val)‖ * error (point (F t.1 t.2.val))) ≤
      η * coefficientErrorCap (O := O) U Q period * coefficientTailSpatialFactor X selection M period W S.value := by
  intro y₀ ker hp f ψ A window F error
  have hHpos (t) : 0 < H t := lt_of_lt_of_le zero_lt_one (hH t)
  have hκ : 0 < 1 / (M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
  have hC := anisotropicSpatialDensityCap_nonneg selection hκ.le
  have hroot (g : G) : |(ker g : ℝ)| ≤ 1 + W := by
    have h := (allocatedPhysicalCube_root_budget B U b S (fun _ => 0) x y₀ (.inl g)).trans hbudget
    change |(ker g : ℝ)| ≤ W at h
    linarith
  have hD (i : α) (g : G) : |(scalarCubeDifferenceMatrix x i g : ℝ)| ≤ S.value :=
    allocatedPhysicalCube_directions_bound B U b S x y₀ i (.inl g)
  have hminor : 1 / (M : ℝ) ≤
      |(Matrix.of (fun i j => (scalarCubeDifferenceMatrix x i (selection j) : ℝ) / (S.value : ℝ))).det| := by
    change 1 / (M : ℝ) ≤ |(normalizedScalarCubePivot selection x).det|
    rw [normalizedScalarCubePivot_det]
    exact hx.1.le
  have hf := (canonicalSpatialSiteDensity_bounds selection ker (scalarCubeDifferenceMatrix x) hp
    hW (Nat.cast_pos.mpr S.positive) (by exact_mod_cast S.positive) hκ hroot hD hminor).1
  have hψ (w) (hw : w ∈ window) : ‖ψ w‖ ≤
      ((period : ℝ) ^ Fintype.card (Unit ⊕ α) * anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X := by
    apply residueSpatialSite_norm_le _ _ period hspatial (fun _ => f) H (by norm_num) hmesh hC
      (fun _ => hf) (fun _ => integerResidueMatrix (principalSpatialColumns (fun _ => (0 : ℤ)) id y₀) period) w
    exact (mem_spatialWindow_scaled_iff H hHpos 4 w).mp hw
  have hA : 0 < A := Finset.prod_pos (fun t _ => Finset.prod_pos (fun i _ =>
    physicalSpatialOutputScale_pos α (hHpos t) (hT t) (Nat.cast_pos.mpr S.positive) i))
  have hcard := spatialWindow_card_anisotropic (α := α) H T hH (by norm_num : (0 : ℝ) ≤ 4)
    (Nat.cast_ne_zero.mpr S.positive.ne') hscale
  norm_num only [show 2 * (4 : ℝ) + 1 = 9 by norm_num] at hcard
  have he (a : cells) (w) : error (point (F a w)) ≤ η * coefficientErrorCap (O := O) U Q period :=
    allocatedRestrictedCoefficientError_bound B U b S hR hσ x u v₀ rows Q d period hperiod hb o bW hη _
  have h := selectedResidue_coefficient_tail stride cells V hV hmass window ψ
    (fun a w => test (F a w)) (fun a w => error (point (F a w))) hA (by positivity)
    (mul_nonneg hη (coefficientErrorCap_nonneg U Q period)) hψ (fun a w => htest (F a w)) he hcard
  convert h using 1
  unfold coefficientTailSpatialFactor
  ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

noncomputable def allocatedErrorKernelCap (η A : ℝ≥0) (V : Fin m → ℝ≥0) : ℝ≥0 :=
  let K : ℝ≥0 := (S.value : ℝ≥0) ^ (layerTailDegree m + 1)
  let D := Fintype.card (Σ a : LayerSamplerAxis I n, O a.1)
  let N := Fintype.card {a // allocatedGridAxis (I := I) U b S.value a}
  (η * A * ∏ j, V j ^ Fintype.card (O j)) * ((K ^ D) ^ N)

noncomputable def allocatedErrorKernelLip (η A : ℝ≥0) (C V : Fin m → ℝ≥0) : ℝ≥0 :=
  let K : ℝ≥0 := (S.value : ℝ≥0) ^ (layerTailDegree m + 1)
  let D := Fintype.card (Σ a : LayerSamplerAxis I n, O a.1)
  let N := Fintype.card {a // allocatedGridAxis (I := I) U b S.value a}
  let M := (K ^ D) ^ N
  (η * A * ∏ j, V j ^ Fintype.card (O j)) *
    ((N * (D * (2 * K ^ 2) * K ^ D) * M) * (∑ j, C j * Fintype.card (J j)) + M * 8)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable (rows : ∀ j, O j → Finset α)

noncomputable def allocatedErrorTorusKernel (η A : ℝ≥0) : (JetAmbientIndex O J → UnitAddCircle) → ℝ :=
  smallBoxTorusKernel (allocatedErrorAmbientKernel B U b S o hR hσ x u v rows η A)

noncomputable def allocatedCoefficientErrorMajorant (η A : ℝ≥0) (d : ℕ)
    (y : EuclideanJetLayers U O) : ℝ :=
  allocatedErrorTorusKernel B U b S o hR hσ x u v rows η A (coveredJetAmbientTorus U d y)

theorem allocatedErrorTorusKernel_bounds (η A : ℝ≥0) (C V : Fin m → ℝ≥0)
    (hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j) :
    (∀ z, 0 ≤ allocatedErrorTorusKernel B U b S o hR hσ x u v rows η A z ∧
      allocatedErrorTorusKernel B U b S o hR hσ x u v rows η A z ≤
        allocatedErrorKernelCap B U b S (O := O) η A V) ∧
    LipschitzWith (allocatedErrorKernelLip B U b S (O := O) η A C V)
      (allocatedErrorTorusKernel B U b S o hR hσ x u v rows η A) := by
  have h := allocatedErrorAmbientKernel_bounds B U b S o hR hσ x u v rows η A C V hC hV
  exact ⟨smallBoxTorusKernel_range _ (NNReal.coe_nonneg _) h.1
      (allocatedErrorAmbientKernel_support B U b S o hR hσ x u v rows η A),
    smallBoxTorusKernel_lipschitz _ h.2 (fun z => (h.1 z).1)
      (allocatedErrorAmbientKernel_support B U b S o hR hσ x u v rows η A)⟩

theorem allocatedCoefficientErrorMajorant_continuous (η A : ℝ≥0) (d : ℕ) (C V : Fin m → ℝ≥0)
    (hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j) :
    Continuous (allocatedCoefficientErrorMajorant B U b S o hR hσ x u v rows η A d) :=
  (allocatedErrorTorusKernel_bounds B U b S o hR hσ x u v rows η A C V hC hV).2.continuous.comp
    (coveredJetAmbientTorus_continuous U d)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

theorem allocatedCoefficientError_le_majorant
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d period : ℕ) [NeZero d] [NeZero period]
    (hperiod : ∀ j, integerScalarLattice (O j) (period : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (η : ℝ≥0) (C V : Fin m → ℝ≥0)
    (hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (y : EuclideanJetLayers U O) :
    restrictedChartDensity (mixedCoveredJetChart U o b hb bW d)
      (mixedCoveredJetRegion (O := O) (E := Q) U o b d (fun j _ => standardLatticeClosedQuarterBox (J j)))
      1 (fun z : MixedCoveredJetSource I O Q n d =>
        allocatedCoveredFixedFactor B U b hR hσ S x u v rows Q d z.1 z.2 *
          ((η : ℝ) / (∏ a, allocatedLongJetOutputScale B U b S (O := O) a))) y ≤
      allocatedCoefficientErrorMajorant B U b S o hR hσ x u v rows η
        (Real.toNNReal (coefficientDeckPeriodCap O Q period)) d y := by
  let chart := mixedCoveredJetChart (O := O) U o b hb bW d
  let region := mixedCoveredJetRegion (O := O) (E := Q) U o b d
    (fun j _ => standardLatticeClosedQuarterBox (J j))
  let A := Real.toNNReal (coefficientDeckPeriodCap O Q period)
  by_cases hy : y ∈ chart '' region
  · obtain ⟨z, hz, rfl⟩ := hy
    have hquarter : ∀ a, |mixedJetAmbientPoint U b o z.1 a| ≤ 1 / 4 := by
      intro a
      exact (hz a.1 (Set.mem_univ _) a.2.1 (Set.mem_univ _)).1 a.2.2
    rw [restrictedChartDensity_apply chart region 1 _
      (mixedCoveredJetChart_injOn U o b hb bW d _
        (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))) hz, one_mul]
    change _ ≤ allocatedErrorTorusKernel B U b S o hR hσ x u v rows η A
      (coveredJetAmbientTorus U d (mixedCoveredJetChart U o b hb bW d z))
    rw [coveredJetAmbientTorus_chart, allocatedErrorTorusKernel,
      smallBoxTorusKernel_local _ (allocatedErrorAmbientKernel_support B U b S o hR hσ x u v rows η A)
        _ (fun a => lt_of_le_of_lt (hquarter a) (by norm_num)),
      allocatedErrorAmbientKernel_quarter _ _ _ _ _ _ _ _ _ _ _ η A z.1 hquarter,
      allocatedCoefficientError_interpolation]
    have hp (j) : integerScalarLattice (O j) (period : ℤ) ≤
        (boundedCoefficientJetMatrix
          (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin (allocatedGridAxis (I := I) U b S.value) u v))
          (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin (allocatedGridAxis (I := I) U b S.value) u v))
          (j.val + 1) (rows j)).mulVecLin.range := by
      rw [← allocatedPartitionedJetMatrix_eq_physical B U b S x u v rows j]
      exact (hperiod j).trans (allocatedPartitionedJetMatrix_kernel_range_le B U b S x u v rows j)
    have hd := coefficientDeckJetDensity_period_bound _ _ rows d period hp z.2
    have hA : coefficientDeckPeriodCap O Q period = (A : ℝ) :=
      (Real.coe_toNNReal _ (coefficientDeckPeriodCap_nonneg O Q period)).symm
    rw [hA] at hd
    apply mul_le_mul_of_nonneg_right _
      ((allocatedGridJetInterpolation_uniform_bounds B U b S hR hσ x u v rows).1 _).1
    apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg (fun j _ => pow_nonneg (hV j).1 _))
    exact mul_le_mul_of_nonneg_left hd η.coe_nonneg
  · rw [restrictedChartDensity_zero chart region 1 _ hy]
    exact ((allocatedErrorTorusKernel_bounds B U b S o hR hσ x u v rows η A C V hC hV).1 _).1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

theorem coefficientDeckPeriodCap_exp_bound {m : ℕ} (O Q : Fin m → Type*)
    [∀ j, Fintype (O j)] [∀ j, Fintype (Q j)] (period : ℕ)
    {D E : ℝ} (hD : 0 ≤ D) (hE : 0 ≤ E) (hm : (m : ℝ) ≤ D)
    (hO : ∀ j, (Fintype.card (O j) : ℝ) ≤ D)
    (hQ : ∀ j, (Fintype.card (Q j) : ℝ) ≤ D)
    (hperiod : (period : ℝ) ≤ Real.exp E) :
    coefficientDeckPeriodCap O Q period ≤ Real.exp (D ^ 3 * E) := by
  have hrow (j : Fin m) : (period : ℝ) ^ Fintype.card (O j) ≤ Real.exp (D * E) :=
    pow_le_exp_mul_of_le_exp (Nat.cast_nonneg _) hperiod hE _ (hO j)
  have hlayer (j : Fin m) : ((period : ℝ) ^ Fintype.card (O j)) ^ Fintype.card (Q j) ≤
      Real.exp (D ^ 2 * E) := by
    exact (pow_le_exp_mul_of_le_exp (by positivity) (hrow j) (mul_nonneg hD hE) _ (hQ j)).trans_eq
      (congrArg Real.exp (by ring))
  unfold coefficientDeckPeriodCap
  simp only [Finset.prod_const, Finset.card_univ]
  calc
    _ ≤ ∏ _j : Fin m, Real.exp (D ^ 2 * E) :=
      Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun j _ => hlayer j)
    _ = Real.exp ((m : ℝ) * (D ^ 2 * E)) := by simp [Real.exp_nat_mul]
    _ ≤ _ := Real.exp_le_exp.mpr (by
      nlinarith [mul_le_mul_of_nonneg_right hm (show 0 ≤ D ^ 2 * E by positivity)])

theorem coefficientLatticeBasis_card_le {m : ℕ} {J Q : Fin m → Type*}
    [∀ j, Fintype (J j)] [∀ j, Fintype (Q j)] {n : Fin m → ℕ}
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (j : Fin m) : Fintype.card (Q j) ≤ Fintype.card (J j) := by
  have h := standardLatticeCoordinates_card (euclideanSubspace (U j)) (bW j) (b j) (hb j)
  rw [Fintype.card_sum, Fintype.card_fin] at h
  omega

theorem jetAmbientIndex_card_le {m : ℕ} (O J : Fin m → Type*)
    [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] {D : ℝ} (hD : 0 ≤ D)
    (hm : (m : ℝ) ≤ D) (hO : ∀ j, (Fintype.card (O j) : ℝ) ≤ D)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ D) :
    (Fintype.card (JetAmbientIndex O J) : ℝ) ≤ D ^ 3 := by
  calc
    _ = ∑ j, (Fintype.card (O j) : ℝ) * Fintype.card (J j) := by
      simp only [JetAmbientIndex, Fintype.card_sigma, Fintype.card_prod, Nat.cast_sum, Nat.cast_mul]
    _ ≤ ∑ _j : Fin m, D * D := Finset.sum_le_sum (fun j _ =>
      mul_le_mul (hO j) (hJ j) (by positivity) hD)
    _ = (m : ℝ) * (D * D) := by simp
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hm (sq_nonneg D)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

def allocatedErrorKernelLog {A : Type*} [Semiring A] (P : A) : A :=
  3 * P ^ 3 + P ^ 2 + 8 * P + 11

theorem allocatedErrorKernelLog_nonneg {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ allocatedErrorKernelLog P := by
  unfold allocatedErrorKernelLog
  positivity

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

theorem allocatedErrorKernel_exp_bounds (η A : ℝ≥0) (C V : Fin m → ℝ≥0)
    {P : ℝ} (hP : 0 ≤ P) (hm : (m : ℝ) ≤ P)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ P)
    (hout : (Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) : ℝ) ≤ P)
    (hO : ∀ j, (Fintype.card (O j) : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hη : η ≤ 1) (hA : (A : ℝ) ≤ Real.exp P)
    (hK : (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ Real.exp P)
    (hC : ∀ j, (C j : ℝ) ≤ Real.exp P) (hV : ∀ j, (V j : ℝ) ≤ Real.exp P) :
    (allocatedErrorKernelCap B U b S (O := O) η A V : ℝ) ≤
      Real.exp (allocatedErrorKernelLog P) ∧
    (allocatedErrorKernelLip B U b S (O := O) η A C V : ℝ) ≤
      Real.exp (allocatedErrorKernelLog P) := by
  let K : ℝ := (S.value : ℝ) ^ (layerTailDegree m + 1)
  let D := Fintype.card (Σ a : LayerSamplerAxis I n, O a.1)
  let N := Fintype.card {a // allocatedGridAxis (I := I) U b S.value a}
  have hK0 : 0 ≤ K := by positivity
  have hN : (N : ℝ) ≤ P :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans haxes
  have hNE : (N : ℝ) ≤ Real.exp P := hN.trans (by linarith [Real.add_one_le_exp P])
  have hDE : (D : ℝ) ≤ Real.exp P := hout.trans (by linarith [Real.add_one_le_exp P])
  have hmE : (m : ℝ) ≤ Real.exp P := hm.trans (by linarith [Real.add_one_le_exp P])
  have hKD : K ^ D ≤ Real.exp (P ^ 2) := by
    simpa only [pow_two] using pow_le_exp_mul_of_le_exp hK0 hK hP D hout
  have hM : (K ^ D) ^ N ≤ Real.exp (P ^ 3) := by
    exact (pow_le_exp_mul_of_le_exp (pow_nonneg hK0 D) hKD (sq_nonneg P) N hN).trans_eq
      (congrArg Real.exp (by ring))
  have hK2 : K ^ 2 ≤ Real.exp (2 * P) := by
    exact (pow_le_pow_left₀ hK0 hK 2).trans_eq (Real.exp_nat_mul P 2).symm
  have hprod : (∏ j, (V j : ℝ) ^ Fintype.card (O j)) ≤ Real.exp (P ^ 3) := by
    calc
      _ ≤ ∏ _j : Fin m, Real.exp (P ^ 2) := Finset.prod_le_prod₀
        (fun _ _ => by positivity) (fun j _ => by
          simpa only [pow_two] using pow_le_exp_mul_of_le_exp (V j).coe_nonneg (hV j) hP _ (hO j))
      _ = Real.exp ((m : ℝ) * P ^ 2) := by simp [Real.exp_nat_mul]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hm (sq_nonneg P)])
  have hfactor : (η : ℝ) * A * (∏ j, (V j : ℝ) ^ Fintype.card (O j)) ≤
      Real.exp (P + P ^ 3) := by
    calc
      _ ≤ 1 * Real.exp P * Real.exp (P ^ 3) := by
        gcongr
        exact_mod_cast hη
      _ = _ := by rw [one_mul, ← Real.exp_add]
  have hsum : (∑ j, (C j : ℝ) * Fintype.card (J j)) ≤ Real.exp (3 * P) := by
    calc
      _ ≤ ∑ _j : Fin m, Real.exp (2 * P) := Finset.sum_le_sum (fun j _ => by
        calc
          _ ≤ Real.exp P * Real.exp P := mul_le_mul (hC j)
            ((hJ j).trans (by linarith [Real.add_one_le_exp P])) (by positivity) (by positivity)
          _ = _ := by rw [← Real.exp_add]; congr 1; ring)
      _ = (m : ℝ) * Real.exp (2 * P) := by simp
      _ ≤ Real.exp P * Real.exp (2 * P) := by gcongr
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  have hfirst : ((N : ℝ) * (D * (2 * K ^ 2) * K ^ D) * (K ^ D) ^ N) *
      (∑ j, (C j : ℝ) * Fintype.card (J j)) ≤ Real.exp (P ^ 3 + P ^ 2 + 7 * P + 2) := by
    calc
      _ ≤ (Real.exp P * (Real.exp P * (Real.exp 2 * Real.exp (2 * P)) * Real.exp (P ^ 2)) *
          Real.exp (P ^ 3)) * Real.exp (3 * P) := by gcongr
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  have hsecond : (K ^ D) ^ N * 8 ≤ Real.exp (P ^ 3 + 8) := by
    calc
      _ ≤ Real.exp (P ^ 3) * Real.exp 8 := by gcongr
      _ = _ := by rw [← Real.exp_add]
  have hinside := add_le_exp_add_one (by positivity) (by positivity) hfirst hsecond
  constructor
  · simp only [allocatedErrorKernelCap, NNReal.coe_mul, NNReal.coe_prod,
      NNReal.coe_pow, NNReal.coe_natCast]
    change (η : ℝ) * A * (∏ j, (V j : ℝ) ^ Fintype.card (O j)) * (K ^ D) ^ N ≤ _
    calc
      _ ≤ Real.exp (P + P ^ 3) * Real.exp (P ^ 3) := by gcongr
      _ = Real.exp (2 * P ^ 3 + P) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by
        unfold allocatedErrorKernelLog
        nlinarith [pow_nonneg hP 3, sq_nonneg P])
  · simp only [allocatedErrorKernelLip, NNReal.coe_mul, NNReal.coe_prod,
      NNReal.coe_pow, NNReal.coe_natCast, NNReal.coe_add, NNReal.coe_sum, NNReal.coe_ofNat]
    change (η : ℝ) * A * (∏ j, (V j : ℝ) ^ Fintype.card (O j)) *
      (((N : ℝ) * (D * (2 * K ^ 2) * K ^ D) * (K ^ D) ^ N) *
        (∑ j, (C j : ℝ) * Fintype.card (J j)) + (K ^ D) ^ N * 8) ≤ _
    calc
      _ ≤ Real.exp (P + P ^ 3) *
          Real.exp ((P ^ 3 + P ^ 2 + 7 * P + 2) + (P ^ 3 + 8) + 1) := by gcongr
      _ = _ := by rw [← Real.exp_add]; congr 1; unfold allocatedErrorKernelLog; ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Classical

theorem physicalCubeCoveredSample_cover {X : Type*} {m q : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (d : ℕ) [NeZero d]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) (v : X → (Unit ⊕ Fin q) → ℤ) :
    d • physicalCubeCoveredSample U d p hm v = physicalCubeCoveredSample U 1 p hm v := by
  funext j
  change quotientIntegerCover (subspaceArrayIntegerLattice (Finset (Fin q)) (U j)) d
    (QuotientAddGroup.mk' _ ((d : ℝ)⁻¹ • _)) = _
  rw [quotientIntegerCover_mk, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne d)), one_smul]
  simp only [physicalCubeCoveredSample, Nat.cast_one, inv_one, one_smul]

theorem physicalCubeEuclideanSample_cover {X : Type*} {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (d : ℕ) [NeZero d]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) (v : X → (Unit ⊕ Fin q) → ℤ) :
    d • physicalCubeEuclideanSample U d p hm v = physicalCubeEuclideanSample U 1 p hm v := by
  unfold physicalCubeEuclideanSample
  rw [← map_nsmul, ← map_nsmul, physicalCubeCoveredSample_cover]

end Erdos3.BooleanCubeKernel

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

theorem coveredJetAmbientTorus_nsmul {m : ℕ} {O J : Fin m → Type*}
    [∀ j, Fintype (O j)] [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (d : ℕ) (y : EuclideanJetLayers U O) :
    coveredJetAmbientTorus U d y = coveredJetAmbientTorus U 1 (d • y) := by
  funext a
  change subspaceAmbientTorus (U a.1) (euclideanSubspaceTorusEquiv (U a.1) (d • y a.1 a.2.1)) a.2.2 =
    subspaceAmbientTorus (U a.1) (euclideanSubspaceTorusEquiv (U a.1) (1 • (d • y a.1 a.2.1))) a.2.2
  rw [one_nsmul]

end Erdos3.VectorPolynomial

namespace Erdos3.BooleanCubeKernel

open Module Submodule VectorPolynomial
open scoped BigOperators Classical NNReal

theorem coveredJetAmbientTorus_sample {X : Type*} {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (d : ℕ) [NeZero d]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) (v : X → (Unit ⊕ Fin q) → ℤ) :
    coveredJetAmbientTorus U d (physicalCubeEuclideanSample U d p hm v) =
      coveredJetAmbientTorus U 1 (physicalCubeEuclideanSample U 1 p hm v) := by
  rw [coveredJetAmbientTorus_nsmul, physicalCubeEuclideanSample_cover]

theorem allocatedCoefficientErrorMajorant_sample {m q : ℕ} {G X : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
    (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
      (allocatedPrincipalSides B U b S))
    (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
      (allocatedPrincipalSides B U b S))
    (rows : ∀ j : Fin m, BoundedBooleanJet (Fin q) (j.val + 1) → Finset α)
    (η A : ℝ≥0) (d : ℕ) [NeZero d]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) (z : X → (Unit ⊕ Fin q) → ℤ) :
    allocatedCoefficientErrorMajorant B U b S o hR hσ x u v rows η A d
        (physicalCubeEuclideanSample U d p hm z) =
      allocatedCoefficientErrorMajorant B U b S o hR hσ x u v rows η A 1
        (physicalCubeEuclideanSample U 1 p hm z) := by
  unfold allocatedCoefficientErrorMajorant
  rw [coveredJetAmbientTorus_sample]

end Erdos3.BooleanCubeKernel

end

end OAI
