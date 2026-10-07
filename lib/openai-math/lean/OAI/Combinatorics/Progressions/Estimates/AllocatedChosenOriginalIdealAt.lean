import OAI.Combinatorics.Progressions.Linear.AllocatedOriginalProjectionBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Matrix NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset (Fin dim))

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides

variable (X : Type*) [Fintype X]

local notation "whole" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n) sides (allocatedPrincipalSides_pos B U b S)
local notation "frozen" => allocatedFrozenTupleWeights (α := Fin dim) B U b S
local notation "long" => allocatedLongTupleWeights (α := Fin dim) B U b S

variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus]
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Module.Basis (Kcov j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

def AllocatedFixedDataSourceAt (η : ℝ) : Prop :=
    ∀ (_hqpos : ∀ t, 0 < q t) (_hσ1 : ∀ j, σ j ≤ 1),
        ∀ [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
        [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
        [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
        [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
        (C : Fin m → ℝ) (_hC : ∀ j, 0 ≤ C j)
        (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
        (_hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) C 1 j)
        (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
        [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
        (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
        [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
        (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides → EuclideanJetLayers U O → ℝ)
        (_hg : ∀ w, Continuous (g w)) (_hg0 : ∀ w z, 0 ≤ g w z)
        (_hlaw : ∀ w, (realDensityMeasure μ (fun z => allocatedCoefficientDensity B U b hb o hR hσ S
          (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d z))).map
          (euclideanCoefficientJetMap U
            (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x w)
            (allocatedPhysicalCubeDirections B U b S x w) rows) =
          realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) (g w))
        (N : X → ℕ) (hN : ∀ t, 0 < N t)
    {W τ C₀ ρ ξ δ mesh : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (_hρ : 0 < ρ)
    (_hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (_hC₀ : 1 ≤ C₀) (_hLC : (S.value : ℝ) ≤ C₀) (_hWC : W ≤ C₀)
    (hξ : 0 < ξ) (_hξ1 : ξ ≤ 1)
    (_hphysicalSize : ∀ t, 8*(1+W)*(q t : ℝ)*ρ ≤ (ξ*τ)*(N t : ℝ))
    (_hmeshSize : anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
    (_hρ8 : 8*(probabilityProfileLipschitz : ℝ) ≤ ρ)
    (_hδ : 0 ≤ δ)
    (_hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
    (_hρmove : Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0)) ≤ δ*ρ)
    (_hmesh : 0 < mesh) (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
    (point : (X → (Unit ⊕ (Fin dim)) → ℤ) → EuclideanJetLayers U O)
    (test : (X → (Unit ⊕ (Fin dim)) → ℤ) → ℂ) (_htest : ∀ v, ‖test v‖ ≤ 1)
    {Cg Z : ℝ} (_hCg : 0 ≤ Cg) (_hZ : 0 < Z)
    (_hcap : ∀ y v, g y (point v) ≤ Cg)
    (_hreferenceMass : ∀ y y₀ (a : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q),
      (∑ v ∈ spatialWindow (trimmedSpatialRootScale τ N q) 4,
        g y (point (physicalResidueReconstruction
          (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y₀)
          (allocatedPhysicalCubeDirections B U b S x y₀) base
          (boundedColumnResidueRepresentative q a) q v))) ≤
        (4 * (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X)) *
          (∏ t, ∏ _i : Unit ⊕ Fin dim, trimmedSpatialRootScale τ N q t)),
    allocatedRefinedTupleMassEstimate B U b hR hσ S x rows X hM selection hx modulus s hA
      q reference residue hb o bW d g N hN hW hτ hξ C₀ ρ δ mesh base cells hmass point test Cg Z η

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset (Fin dim))

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides

variable (X : Type*) [Fintype X]

local notation "whole" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n) sides (allocatedPrincipalSides_pos B U b S)
local notation "frozen" => allocatedFrozenTupleWeights (α := Fin dim) B U b S
local notation "long" => allocatedLongTupleWeights (α := Fin dim) B U b S

variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus]
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Module.Basis (Kcov j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

theorem allocatedFixedData_source_of_pointwise
    (hRefined : 0 < residueRefinedPeriod modulus q)
    (hsize : ∀ a, (Fintype.card (Fin dim) + 1) * residueRefinedPeriod modulus q ≤ lengths a)
    (href : ∀ u r, principalResidueLabel (residueRefinedPeriod modulus q) (reference u r) = r)
    (hperiod : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hspatial : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage
        (selectedSpatialPivot (fun a => (0 : ℤ) + (x a none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun a => (0 : ℤ) + (x a none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
    (hr : ∀ u r v, (allocatedLongResidueWeights B U b S (residueRefinedPeriod modulus q)
      hRefined r hsize).weight v ≠ 0 → ∀ j,
      integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) modulus = residue u r j)
    {η : ℝ}
    (hpoint : ∀ (hσ1 : ∀ j, σ j ≤ 1) u r (z : AllocatedLongJetRows B U b S O),
      |(allocatedLongResidueWeights B U b S (residueRefinedPeriod modulus q) hRefined r hsize).mean
          (fun v => (∏ a, allocatedLongJetOutputScale B U b S (O := O) a) *
            allocatedLongJetDensity B U b hR hσ S x u v rows s hA hσ1 z) -
        allocatedLongJetProxy B U b S x u rows s hA modulus (residue u r) z| ≤ η) :
    AllocatedFixedDataSourceAt B U b hR hσ S x rows X hM selection hx modulus s hA
      q reference residue hb o bW d η := by
  intro hqpos hσ1 _ _ _ _ C hC hchart hsmall μ _ _ ν _ _ g hg hg0 hlaw
    N hN W τ C₀ ρ ξ δ mesh hW hτ hρ hbudget hC₀ hLC hWC hξ hξ1
    hphysicalSize hmeshSize hρ8 hδ hρshift hρmove hmesh base cells hmass point test htest
    Cg Z hCg hZ hcap hreferenceMass
  unfold allocatedRefinedTupleMassEstimate
  intro coefficientScale chart region H T V hV hp f ψ A E₀ Γ E₁ Esite
    window F factor proxy error source target budget
  have hκ : 0 < 1 / (M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
  have hE₀ : 0 ≤ E₀ := anisotropicSpatialError_nonneg selection _ M hκ.le
    (zero_le_one.trans hC₀) hρ.le hξ.le
  have hcap₀ := anisotropicSpatialDensityCap_nonneg selection hκ.le
  have hlip := anisotropicSpatialDensityLip_nonneg selection hκ.le
  have hEsite : 0 ≤ Esite := by dsimp only [Esite, E₁, Γ]; positivity
  have hApos : 0 < A := by
    apply Finset.prod_pos
    intro t _
    apply Finset.prod_pos
    intro i _
    have hscale := trimmedSpatial_scales_pos hW hτ N q t (hN t) (hqpos t)
    exact physicalSpatialOutputScale_pos (Fin dim) hscale.1 hscale.2 (Nat.cast_pos.mpr S.positive) i
  apply allocatedTuple_normalized_residue_comparison B U b S (residueRefinedPeriod modulus q)
    hRefined hsize source target budget (Z : ℂ)
  intro u r
  have hdiv : modulus ∣ residueRefinedPeriod modulus q := ⟨∏ a, q a, rfl⟩
  have hcomparison := allocatedOriginal_refined_density_comparison B U b hR hσ S x u rows s hA
    hb o hσ1 C hC hchart hsmall bW d μ ν (fun v => g (principalAxisJoin grid u v))
    (fun v => hg (principalAxisJoin grid u v)) (fun v => hg0 (principalAxisJoin grid u v))
    (fun v => hlaw (principalAxisJoin grid u v))
    (residueRefinedPeriod modulus q) hRefined r hsize (reference u r) (href u r)
    modulus hdiv hperiod (residue u r) (hr u r) (hpoint hσ1 u r)
    selection hκ hx N q hN hqpos hW hτ hρ hbudget hC₀ hLC hWC hξ hξ1
    hphysicalSize hmeshSize hρ8 hspatial (stride_mul_dvd_residueRefinedPeriod modulus q)
    hδ hρshift hρmove hmesh base cells hmass point test htest hCg hZ
    (fun v _ z => hcap (principalAxisJoin grid u v) z)
  have hmassBound := coarse_reference_mean_spatial_budget
    (allocatedLongResidueWeights B U b S (residueRefinedPeriod modulus q) hRefined r hsize)
    q cells V hV hmass
    (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u (reference u r)))
    (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u (reference u r)))
    base H T (Nat.cast_ne_zero.mpr S.positive.ne') (fun t => trimmedSpatial_scale_ratio hW N q t)
    hApos point (fun v => g (principalAxisJoin grid u v))
    (fun v => hg0 (principalAxisJoin grid u v)) test htest
    (offset := Cg * (24 * (probabilityProfileLipschitz : ℝ) *
      Fintype.card (Option (LayerSamplerVariables G I n B) × X) / ρ) / Z)
    hEsite hZ (fun v _ a => hreferenceMass (principalAxisJoin grid u v)
      (principalAxisJoin grid u (reference u r)) a.val)
  exact hcomparison.trans (add_le_add hmassBound le_rfl)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset (Fin dim))

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides

variable (X : Type*) [Fintype X]

local notation "whole" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n) sides (allocatedPrincipalSides_pos B U b S)
local notation "frozen" => allocatedFrozenTupleWeights (α := Fin dim) B U b S
local notation "long" => allocatedLongTupleWeights (α := Fin dim) B U b S

variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus]
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Module.Basis (Kcov j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S) → EuclideanJetLayers U O → ℝ)
variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (C₀ ρ δ mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (Cg Z : ℝ)

theorem allocatedRefinedTupleDifference_decomposition :
    allocatedRefinedTupleDifference B U b hR hσ S x rows X hM selection hx modulus s hA
      q reference residue hb o bW d g N hN hW hτ hξ mesh base cells hmass point test Z =
    allocatedProjectedTupleSource B U b S x X q g N hN hW hτ hξ base cells hmass point test Z -
    allocatedRefinedTupleReference (τ := τ) (ξ := ξ) B U b hR hσ S x rows X hM selection hx modulus s hA
      q reference residue hb o bW d N hW mesh base cells point test Z := rfl

noncomputable def allocatedOriginalTupleDifference
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j e, coefficients (poly j) e ∈ U j) : ℂ :=
    allocatedOriginalTupleSource B U b hR hσ S x X q hb o N hN hW hτ hξ base cells hmass test Z poly hmem -
    allocatedRefinedTupleReference (τ := τ) (ξ := ξ) B U b hR hσ S x rows X hM selection hx modulus s hA
      q reference residue hb o bW d N hW mesh base cells point test Z

variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

theorem allocatedOriginalTupleDifference_bound {δ ε : ℝ}
    (hprojection : ‖allocatedOriginalTupleSource B U b hR hσ S x X q hb o N hN hW hτ hξ base cells hmass test Z poly hmem -
      allocatedProjectedTupleSource B U b S x X q g N hN hW hτ hξ base cells hmass point test Z‖ ≤ δ)
    (hcomparison : ‖allocatedRefinedTupleDifference B U b hR hσ S x rows X hM selection hx modulus s hA
      q reference residue hb o bW d g N hN hW hτ hξ mesh base cells hmass point test Z‖ ≤ ε) :
    ‖allocatedOriginalTupleDifference B U b hR hσ S x rows X hM selection hx modulus s hA
      q reference residue hb o bW d N hN hW hτ hξ mesh base cells hmass point test Z poly hmem‖ ≤ δ + ε := by
  rw [allocatedRefinedTupleDifference_decomposition] at hcomparison
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hprojection hcomparison)

theorem allocatedOriginalTupleDifference_exp_bound {E : ℝ} (hZ : 1 / 2 ≤ Z)
    (hprojection : ‖allocatedOriginalTupleSource B U b hR hσ S x X q hb o N hN hW hτ hξ base cells hmass test Z poly hmem -
      allocatedProjectedTupleSource B U b S x X q g N hN hW hτ hξ base cells hmass point test Z‖ ≤
        (2 * Real.exp (-(E + 4)) + Real.exp (-(E + 4))) / Z)
    (hcomparison : ‖allocatedRefinedTupleDifference B U b hR hσ S x rows X hM selection hx modulus s hA
      q reference residue hb o bW d g N hN hW hτ hξ mesh base cells hmass point test Z‖ ≤ Real.exp (-(E + 1))) :
    ‖allocatedOriginalTupleDifference B U b hR hσ S x rows X hM selection hx modulus s hA
      q reference residue hb o bW d N hN hW hτ hξ mesh base cells hmass point test Z poly hmem‖ ≤ Real.exp (-E) := by
  exact (allocatedOriginalTupleDifference_bound B U b hR hσ S x rows X hM selection hx modulus s hA
    q reference residue hb o bW d g N hN hW hτ hξ mesh base cells hmass point test Z poly hmem
    hprojection hcomparison).trans (originalTupleProjectionPrecision_bound hZ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Matrix NNReal Classical

universe uX

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "rows" => (fun j : Fin m => (Subtype.val : jets j → Finset (Fin dim)))

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides

variable (X : Type uX) [Fintype X] [DecidableEq X]

local notation "whole" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n) sides (allocatedPrincipalSides_pos B U b S)
local notation "frozen" => allocatedFrozenTupleWeights (α := Fin dim) B U b S
local notation "long" => allocatedLongTupleWeights (α := Fin dim) B U b S

variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus]
variable (s : ∀ j : Fin m, BoundedBooleanJet (Fin dim) (j.val + 1) ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j : Fin m, ((scalarKernelIntegerJet x (j.val + 1)
  (Subtype.val : BoundedBooleanJet (Fin dim) (j.val + 1) → Finset (Fin dim))).submatrix id (s j)).det ≠ 0)
variable (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  ∀ j : Fin m, Matrix (BoundedBooleanJet (Fin dim) (j.val + 1))
    (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Module.Basis (Kcov j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

def AllocatedChosenOriginalIdealAt (Pbase : ℝ) (Kproj : ℕ) (P E η : ℝ) (δideal : ℝ≥0) : Prop :=
    ∀ (_hP : 0 ≤ P) (_hE : 0 ≤ E)
    (_hmP : ((m + 1 : ℕ) : ℝ) ≤ P) (_hdimP : ((dim + 1 : ℕ) : ℝ) ≤ P)
    (_hGP : (Fintype.card G : ℝ) ≤ P) (_hXP : (Fintype.card X : ℝ) ≤ P)
    (_hMP : (M : ℝ) ≤ Real.exp P) (_hmodulus : modulus ≤ M ^ (m + 1))
    (_hqpos : ∀ t, 0 < q t) (_hσ1 : ∀ j, σ j ≤ 1),
    let indices := PrincipalTupleIndex B (layerSamplerDegree I n)
    let ξ := normalizedTupleNarrowWidth X indices selection M P (E + 2)
    let hξ := normalizedTupleNarrowWidth_pos X indices selection M P (E + 2)
    ξ ≤ 1 ∧ ξ⁻¹ ≤ Real.exp (normalizedTupleWidthLog indices selection P (E + 2)) ∧
    ∀ [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
        [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
        [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
        [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
        (C : Fin m → ℝ) (_hC : ∀ j, 0 ≤ C j)
        (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
        (_hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) C 1 j)
        (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
        [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
        (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
        [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
        (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides → EuclideanJetLayers U jets → ℝ)
        (_hg : ∀ w, Continuous (g w)) (_hg0 : ∀ w z, 0 ≤ g w z)
        (_hlaw : ∀ w, (realDensityMeasure μ (fun z => allocatedCoefficientDensity B U b hb o hR hσ S
          (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d z))).map
          (euclideanCoefficientJetMap U
            (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x w)
            (allocatedPhysicalCubeDirections B U b S x w) rows) =
          realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : jets j => ν j))) (g w))
        (_hprojection : AllocatedOriginalSourceProjectionAt.{uX} B U b hR hσ S x hb o d g Pbase Kproj)
    {W τ C₀ Cg Z growth l : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ)
    (_hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (_hC₀ : 1 ≤ C₀) (_hLC : (S.value : ℝ) ≤ C₀) (_hWC : W ≤ C₀)
    (_hCg : 0 ≤ Cg) (_hZ : 1 / 2 ≤ Z)
    (_hgrowth : growth ≤ Real.exp P) (_hWscale : W ≤ growth * (S.value : ℝ))
    (_hl : 0 ≤ l) (_hC₀l : C₀ ≤ Real.exp l) (_hWl : W ≤ Real.exp l)
    (_hCgl : Cg ≤ Real.exp l)
    (_hentryl : allocatedPhysicalEntryBudget B U b S (fun _ => 0) ≤ Real.exp l)
    (_hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp l)
    (_hql : ∀ t, (q t : ℝ) ≤ Real.exp l) (_hτl : τ⁻¹ ≤ Real.exp l),
    let Centry := allocatedPhysicalEntryBudget B U b S (fun _ => 0)
    let δsp := normalizedTupleRadius X selection M P (E + 2) W
    let mesh := δsp / 4
    let ρ := normalizedTupleResolution X indices selection M P (E + 2) C₀ W Cg Centry
    0 < δsp ∧ 0 < mesh ∧ 0 < ρ ∧
    δsp⁻¹ ≤ Real.exp (3 * normalizedTupleLateBudget X indices selection P (E + 2) l + 8) ∧
    mesh⁻¹ ≤ Real.exp (3 * normalizedTupleLateBudget X indices selection P (E + 2) l + 8) ∧
    ρ ≤ Real.exp (3 * normalizedTupleLateBudget X indices selection P (E + 2) l + 8) ∧
    ∀ {Q : ℝ} (_hPbaseQ : Pbase ≤ Q) (_hlQ : l ≤ Q) (_hEQ : E + 1 ≤ Q)
    (_hwidthQ : normalizedTupleWidthLog indices selection P (E + 2) ≤ Q)
    (_hXQ : (Fintype.card X : ℝ) ≤ Q)
    (_hdimQ : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ Q),
    ∀ (N : X → ℕ) (hN : ∀ t, 0 < N t)
    (_hside : ∀ t, Real.exp (normalizedTupleSideLog X indices selection P (E + 2) l) ≤ (N t : ℝ))
    (_hsizeProj : ∀ t, Real.exp ((Q + Kproj) ^ Kproj) ≤ (N t : ℝ))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
    {rank : ℝ}
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) rank (U j) (poly j))
    (_hRank : Real.exp ((Q + Kproj) ^ Kproj) ≤ rank)
    (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (_hcells : cells.Nonempty)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := indices) W τ ξ N) z)
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) (_htest : ∀ site v, ‖test site v‖ ≤ 1),
    let point := physicalCubeEuclideanSample U d poly hmem
    let siteTest := physicalCubeSiteTest test
    ∀
    (_hcap : ∀ y v, g y (point v) ≤ Cg)
    (_hreferenceMass : ∀ y y₀ (a : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q),
      (∑ v ∈ spatialWindow (trimmedSpatialRootScale τ N q) 4,
        g y (point (physicalResidueReconstruction
          (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y₀)
          (allocatedPhysicalCubeDirections B U b S x y₀) base
          (boundedColumnResidueRepresentative q a) q v))) ≤
        (4 * (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X)) *
          (∏ t, ∏ _i : Unit ⊕ Fin dim, trimmedSpatialRootScale τ N q t)),
    allocatedRefinedReferenceTailBound (τ := τ) (ξ := ξ)
      B U b hR hσ S x rows X hM selection hx modulus q reference hb o bW d
      N hW mesh base cells point siteTest η (Z * Real.exp (-(E + 4))) →
    ‖allocatedRefinedTupleReference (τ := τ) (ξ := ξ)
        B U b hR hσ S x rows X hM selection hx modulus s hA q reference residue hb o bW d
        N hW mesh base cells point siteTest Z -
      allocatedRefinedIdealReference (τ := τ) (ξ := ξ)
        B U b hR hσ S x rows X hM selection hx modulus q reference residue hb o bW d
        N hW mesh base cells point siteTest Z δideal‖ ≤ Real.exp (-(E + 4)) →
    ‖allocatedOriginalTupleSource B U b hR hσ S x X q hb o N hN hW hτ hξ base cells hmass
        siteTest Z poly hmem -
      allocatedRefinedIdealReference (τ := τ) (ξ := ξ)
        B U b hR hσ S x rows X hM selection hx modulus q reference residue hb o bW d
        N hW mesh base cells point siteTest Z δideal‖ ≤ Real.exp (-E)

end Erdos3.VectorPolynomial

end

end OAI
