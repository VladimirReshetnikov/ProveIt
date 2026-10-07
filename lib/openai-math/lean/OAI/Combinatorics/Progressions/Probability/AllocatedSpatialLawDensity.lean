import OAI.Combinatorics.Progressions.Lattices.AllocatedResidueSpatialDensity

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "rootAt" => (fun w => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u w))
local notation "dirsAt" => (fun w => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u w))
local notation "axis" => coefficientJetAxisEquiv O I n
local notation "scale" => (∏ a, allocatedLongJetOutputScale B U b S (O := O) a)

variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B α C 1 j)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (g : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S) → EuclideanJetLayers U O → ℝ)
variable (hg : ∀ w, Continuous (g w)) (hg0 : ∀ w z, 0 ≤ g w z)
variable (hlaw : ∀ w, (realDensityMeasure μ (fun z => allocatedCoefficientDensity B U b hb o hR hσ S
    (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d z))).map
    (euclideanCoefficientJetMap U
      (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin (allocatedGridAxis (I := I) U b S.value) u w))
      (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin (allocatedGridAxis (I := I) U b S.value) u w)) rows) =
    realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) (g w))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (O := O) (E := E) U o b d
  (fun j _ => standardLatticeClosedQuarterBox (J j))

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]

variable [DecidableEq G] {D N : Type*} [Fintype D] [Fintype N] [DecidableEq N]
variable (c : D → N → ℤ) (index : D → N → PrincipalTupleIndex B (layerSamplerDegree I n))
variable (spatialRoot : G → ℤ) (selection : α ↪ G)
variable (hP : (selectedSpatialPivot spatialRoot (scalarCubeDifferenceMatrix x) selection).det ≠ 0)
variable (H : D → ℝ) (Q : D → N → ℝ) (hH : ∀ t, 0 < H t) (hQ : ∀ t j, 0 < Q t j)

local notation "spatialScale" => (∏ t, ∏ _i : Unit ⊕ α, H t : ℝ)
local notation "spatialLaw" => allocatedSpatialOutputLaw B U b S u c index x spatialRoot H Q hH hQ

include hσ1 hC hchart hsmall hg hg0 hlaw in
theorem allocatedSpatialLaw_density_comparison
    {M : ℕ} (hM : 0 < M) (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (hroot : ∀ j, |spatialRoot j| ≤ (S.value : ℤ))
    (modulus : ℕ) [NeZero modulus] (hm : 0 < modulus)
    (hp : integerScalarLattice (Unit ⊕ α) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot spatialRoot (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns spatialRoot (scalarCubeDifferenceMatrix x) selection))
    (label : PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
      (fun a => layerSamplerDegree I n a.val) → Option α → ZMod modulus)
    (hsize : ∀ t, (Fintype.card α + 1) * modulus ≤ principalAxisLength (fun a => ¬grid a) sides t)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (hv₀ : principalResidueLabel modulus v₀ = label)
    (hperiod : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    {ε : ℝ} (hpoint : ∀ z, |(allocatedLongResidueWeights B U b S modulus hm label hsize).mean
      (fun w => scale * allocatedLongJetDensity B U b hR hσ S x u w rows s hA hσ1 z) -
        allocatedLongJetProxy B U b S x u rows s hA modulus residue z| ≤ ε)
    {ρ ξ mesh : ℝ} (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hwidth : ∀ t j, ((|c t j| : ℤ)+(sides (index t j) : ℤ) : ℝ)*Q t j ≤ ξ*H t)
    (hρ : 0 < ρ) (hscale : ∀ t, ρ ≤ H t/S.value) (hscaleQ : ∀ t j, ρ ≤ Q t j)
    (hlarge : smoothSpatialMeshThreshold α G N S.value ≤ ρ) (hmesh : 0 < mesh)
    (tv : Finset (D → (Unit ⊕ α) → ℤ))
    (htv : ∀ v ∈ tv, ∀ t i, |((spatialStar (v t) i : ℤ) : ℝ)/H t| ≤ 1)
    (point : (D → (Unit ⊕ α) → ℤ) → EuclideanJetLayers U O)
    (test : (D → (Unit ⊕ α) → ℤ) → ℂ) (htest : ∀ v ∈ tv, ‖test v‖ ≤ 1)
    (cap : (D → (Unit ⊕ α) → ℤ) → ℝ)
    (hcap : ∀ w, (allocatedLongResidueWeights B U b S modulus hm label hsize).weight w ≠ 0 →
      ∀ v ∈ tv, g w (point v) ≤ cap v)
    {Z : ℝ} (hZ : 0 < Z) :
    let spatialProxy := fun v => allocatedSpatialProxy B U b S u c index x spatialRoot selection hP H hH
      modulus label mesh v / (spatialScale : ℂ)
    let δ := smoothVectorSpatialError D N selection M S.value modulus ρ ξ mesh / spatialScale
    let proxy := restrictedChartDensity chart region 1 (fun z : MixedCoveredJetSource I O E n d =>
      allocatedCoveredFixedFactor B U b hR hσ S x u v₀ rows E d z.1 z.2 *
        (allocatedLongJetProxy B U b S x u rows s hA modulus residue (fun a => axis z.1 a.val) / scale))
    let error := restrictedChartDensity chart region 1 (fun z : MixedCoveredJetSource I O E n d =>
      allocatedCoveredFixedFactor B U b hR hσ S x u v₀ rows E d z.1 z.2 * (ε / scale))
    ‖(allocatedLongResidueWeights B U b S modulus hm label hsize).complexMean
        (fun w => ∑ v : tv, test v.val * (((spatialLaw w v.val).toReal : ℂ) * (g w (point v.val) : ℂ))) /
        (Z : ℂ) - (∑ v : tv, test v.val * (spatialProxy v.val * (proxy (point v.val) : ℂ))) / (Z : ℂ)‖ ≤
      (∑ v : tv, (δ * cap v.val + ‖spatialProxy v.val‖ * error (point v.val))) / Z := by
  intro spatialProxy δ proxy error
  have hspatialScale : 0 < spatialScale :=
    Finset.prod_pos (fun t _ => Finset.prod_pos (fun _ _ => hH t))
  have hspatialScaleC : (spatialScale : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hspatialScale.ne'
  have hδ : 0 ≤ δ := div_nonneg
    (smoothVectorSpatialError_nonneg D N selection M S.value modulus hρ.le hξ0 hmesh.le) hspatialScale.le
  have hspatial (w) (hw : (allocatedLongResidueWeights B U b S modulus hm label hsize).weight w ≠ 0)
      (v : tv) : ‖((spatialLaw w v.val).toReal : ℂ) - spatialProxy v.val‖ ≤ δ := by
    have he := allocatedSpatial_site_error B U b S u c index x spatialRoot selection hP H Q hH hQ
      hM hx hroot modulus hp hξ0 hξ1 hwidth hρ hscale hscaleQ hlarge hmesh w v.val (htv v.val v.property)
    rw [allocatedLongResidueWeights_support_label B U b S modulus hm label hsize w hw] at he
    have hid (a : ℝ) (b : ℂ) : (a : ℂ) - b / (spatialScale : ℂ) =
        ((spatialScale * a : ℝ) - b) / (spatialScale : ℂ) := by
      rw [Complex.ofReal_mul, sub_div, mul_div_cancel_left₀ _ hspatialScaleC]
    change ‖((spatialLaw w v.val).toReal : ℂ) - _ / (spatialScale : ℂ)‖ ≤ δ
    rw [hid, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hspatialScale]
    exact div_le_div_of_nonneg_right he hspatialScale.le
  exact allocatedResidue_spatial_density_comparison B U b hR hσ S x u rows s hA
    hb o hσ1 C hC hchart hsmall bW d μ ν g hg hg0 hlaw modulus hm label hsize v₀ hv₀ hperiod residue hpoint
    (fun v : tv => point v.val) (fun w (v : tv) => ((spatialLaw w v.val).toReal : ℂ))
    (fun v : tv => spatialProxy v.val) (fun v : tv => test v.val) (fun _ => δ) (fun v : tv => cap v.val)
    (fun _ => hδ) (fun v => htest v.val v.property) hspatial
    (fun w hw v => hcap w hw v.val v.property) hZ

end Erdos3.VectorPolynomial

end

end OAI
