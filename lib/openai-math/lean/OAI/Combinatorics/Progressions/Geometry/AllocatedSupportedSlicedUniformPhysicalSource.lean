import OAI.Combinatorics.Progressions.Estimates.AllocatedFiniteModelPhysicalExpansion
import OAI.Combinatorics.Progressions.Estimates.AllocatedSlicedFiniteModelComparison
import OAI.Combinatorics.Progressions.Estimates.AllocatedSlicedIdealCutoff
import OAI.Combinatorics.Progressions.Probability.AllocatedPhysicalExpansionMass
import OAI.Combinatorics.Progressions.Sampling.AllocatedSupportedSlicedFullGridSite

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))

variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell grid
local notation "height" => (fun a : gridAxes => basisAxisScale (b (Sigma.fst (ig a))) (Sigma.snd (ig a)))

variable (x : G → IntegerScalarCubeBox α S.value)
variable (u₀ : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (hu₀ : ((containedSupportedProgressionAxisLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell (allocatedGridAxis (I := I) U b S.value))).weight u₀ ≠ 0)
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)] (d : ℕ) [NeZero d]
variable (hperiod : ∀ j, integerScalarLattice ((fun j : Fin m => {t : Finset α // t ∈ rowSets j}) j) (q : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) ((fun j => (Subtype.val : rowSets j → Finset α)) j)).mulVecLin.range)
local notation "root" u => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v₀)
local notation "dirs" u => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v₀)
local notation "residue" u:max => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v₀) q)

include hu₀ hperiod in

theorem allocatedSupportedSlicedDeck_density_constant
    (u : PrincipalAxisTuples (α := α) grid (allocatedPrincipalSides B U b S))
    (hu : (gridLaw).weight u ≠ 0) (z : ∀ j, rowTypes j → Q j → ZMod d) :
    coefficientDeckJetDensity (root u) (dirs u) rows d z =
      coefficientDeckJetDensity (root u₀) (dirs u₀) rows d z := by
  have he := allocatedSupportedSlicedDeck_law_constant B U b S x H step c hH hsubset q r hcell
    u u₀ hu hu₀ v₀ rows Q hperiod d
  unfold coefficientDeckJetDensity
  convert congrArg (fun p : PMF (∀ j, rowTypes j → Q j → ZMod d) =>
    (Fintype.card (∀ j, rowTypes j → Q j → ZMod d) : ℝ) * (p z).toReal) he using 1 <;> congr!

include hu₀ hperiod in

theorem allocatedSupportedSlicedCoveredFactor_mean
    (z : ∀ j, (I j → rowTypes j → ℝ) × (Fin (n j) → rowTypes j → ℤ))
    (deck : ∀ j, rowTypes j → Q j → ZMod d) :
    (gridLaw).mean (fun u => allocatedCoveredFixedFactor B U b hR hσ S x u v₀ rows Q d z deck) =
      allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q r hcell x
        (fun a => coefficientJetAxisEquiv rowTypes I n z a.val) *
        coefficientDeckJetDensity (root u₀) (dirs u₀) rows d deck / coveredJetArrayScale (O := rowTypes) U := by
  have he : (gridLaw).mean (fun u => allocatedCoveredFixedFactor B U b hR hσ S x u v₀ rows Q d z deck) =
      (gridLaw).mean (fun u => allocatedGridJetDensity B U b hR hσ S x u v₀ rows
        (fun a => coefficientJetAxisEquiv rowTypes I n z a.val) *
        coefficientDeckJetDensity (root u₀) (dirs u₀) rows d deck / coveredJetArrayScale (O := rowTypes) U) := by
    apply FiniteProbabilityWeights.mean_congr_on_support
    intro u hu
    unfold allocatedCoveredFixedFactor
    rw [allocatedSupportedSlicedDeck_density_constant B U b S rowSets H step c hH hsubset q r hcell x u₀ hu₀ v₀ Q d hperiod u hu]
  rw [he]
  simp only [div_eq_mul_inv, FiniteProbabilityWeights.mean_mul_const]
  rw [allocatedSupportedSlicedFullGridDensity_mean B U b hR hσ S rowSets H step c hH hsubset q r hcell x v₀]

include hu₀ in

theorem allocatedSupportedSlicedLongProfile_constant
    (u : PrincipalAxisTuples (α := α) grid (allocatedPrincipalSides B U b S))
    (hu : (gridLaw).weight u ≠ 0)
    (f : ((Σ a : {a // ¬grid a}, rowTypes a.val.1) → ℝ) → ℝ)
    (z : AllocatedLongJetRows B U b S rowTypes) :
    allocatedLongProfileDensity B U b S x rows q (residue u) f z =
      allocatedLongProfileDensity B U b S x rows q (residue u₀) f z := by
  have he : (residue u) = (residue u₀) := by
    funext j
    exact allocatedSupportedSlicedNonkernel_residue_constant B U b S x H step c hH hsubset q r hcell
      u u₀ hu hu₀ v₀ rows j
  rw [he]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))

variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell grid
local notation "height" => (fun a : gridAxes => basisAxisScale (b (Sigma.fst (ig a))) (Sigma.snd (ig a)))

variable (x : G → IntegerScalarCubeBox α S.value)
variable (u₀ : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (hu₀ : ((containedSupportedProgressionAxisLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell (allocatedGridAxis (I := I) U b S.value))).weight u₀ ≠ 0)
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)] (d : ℕ) [NeZero d]
variable (hperiod : ∀ j, integerScalarLattice ((fun j : Fin m => {t : Finset α // t ∈ rowSets j}) j) (q : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) ((fun j => (Subtype.val : rowSets j → Finset α)) j)).mulVecLin.range)
local notation "root" u => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v₀)
local notation "dirs" u => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v₀)
local notation "residue" u:max => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v₀) q)

include hu₀ hperiod in

theorem allocatedSupportedSlicedMaskedCoveredFactor_mean
    (f : ((Σ a : {a // ¬grid a}, rowTypes a.val.1) → ℝ) → ℝ)
    (z : ∀ j, (I j → rowTypes j → ℝ) × (Fin (n j) → rowTypes j → ℤ))
    (deck : ∀ j, rowTypes j → Q j → ZMod d) :
    (gridLaw).mean (fun u => allocatedCoveredFixedFactor B U b hR hσ S x u v₀ rows Q d z deck *
      allocatedLongProfileDensity B U b S x rows q (residue u) f
        (fun a => coefficientJetAxisEquiv rowTypes I n z a.val)) =
    (allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q r hcell x
        (fun a => coefficientJetAxisEquiv rowTypes I n z a.val) *
      coefficientDeckJetDensity (root u₀) (dirs u₀) rows d deck / coveredJetArrayScale (O := rowTypes) U) *
      allocatedLongProfileDensity B U b S x rows q (residue u₀) f
        (fun a => coefficientJetAxisEquiv rowTypes I n z a.val) := by
  have he : (gridLaw).mean (fun u => allocatedCoveredFixedFactor B U b hR hσ S x u v₀ rows Q d z deck *
      allocatedLongProfileDensity B U b S x rows q (residue u) f
        (fun a => coefficientJetAxisEquiv rowTypes I n z a.val)) =
    (gridLaw).mean (fun u => allocatedCoveredFixedFactor B U b hR hσ S x u v₀ rows Q d z deck *
      allocatedLongProfileDensity B U b S x rows q (residue u₀) f
        (fun a => coefficientJetAxisEquiv rowTypes I n z a.val)) := by
    apply FiniteProbabilityWeights.mean_congr_on_support
    intro u hu
    rw [allocatedSupportedSlicedLongProfile_constant B U b S rowSets H step c hH hsubset q r hcell x
      u₀ hu₀ v₀ u hu]
  rw [he, FiniteProbabilityWeights.mean_mul_const,
    allocatedSupportedSlicedCoveredFactor_mean B U b hR hσ S rowSets H step c hH hsubset q r hcell x
      u₀ hu₀ v₀ Q d hperiod]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))

variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell grid
local notation "height" => (fun a : gridAxes => basisAxisScale (b (Sigma.fst (ig a))) (Sigma.snd (ig a)))

variable (x : G → IntegerScalarCubeBox α S.value)
variable (u₀ : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (hu₀ : ((containedSupportedProgressionAxisLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell (allocatedGridAxis (I := I) U b S.value))).weight u₀ ≠ 0)
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)] (d : ℕ) [NeZero d]
variable (hperiod : ∀ j, integerScalarLattice ((fun j : Fin m => {t : Finset α // t ∈ rowSets j}) j) (q : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) ((fun j => (Subtype.val : rowSets j → Finset α)) j)).mulVecLin.range)
local notation "root" u => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v₀)
local notation "dirs" u => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v₀)
local notation "residue" u:max => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v₀) q)

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "quarter" => (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "region" => mixedCoveredJetRegion (E := Q) U o b d quarter
local notation "y₀" => principalAxisJoin grid u₀ v₀
local notation "gridDensity" => allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q r hcell x

include hu₀ hperiod in

theorem allocatedSupportedSlicedMaskedProfile_chart_mean
    (f : ((Σ a : {a // ¬grid a}, rowTypes a.val.1) → ℝ) → ℝ)
    (z : MixedCoveredJetSource I rowTypes Q n d) (hz : z ∈ region) :
    (gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
      (principalAxisJoin grid u v₀) q f (chart z)) =
    gridDensity (allocatedFullGridRowsOfMixed B U b S rowSets z.1) *
      allocatedWholeMaskedGridlessProfile B U b S x y₀ rows hb o bW d q f (chart z) := by
  have hinj := mixedCoveredJetChart_injOn U o b hb bW d quarter
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
  simp only [allocatedWholeMaskedCoveredProfile, allocatedWholeMaskedGridlessProfile,
    principalAxisRestrict_join_left, principalAxisRestrict_join_right,
    allocatedCoveredProfileDensity, allocatedGridlessCoveredProfile,
    restrictedChartDensity_apply _ _ _ _ hinj hz, one_mul]
  have h := allocatedSupportedSlicedMaskedCoveredFactor_mean B U b hR hσ S rowSets
    H step c hH hsubset q r hcell x u₀ hu₀ v₀ Q d hperiod f z.1 z.2
  convert h using 1 <;> try rfl
  change gridDensity (fun a => coefficientJetAxisEquiv rowTypes I n z.1 a.val) *
    (coefficientDeckJetDensity (root u₀) (dirs u₀) rows d z.2 / coveredJetArrayScale (O := rowTypes) U *
      allocatedLongProfileDensity B U b S x rows q (residue u₀) f
        (fun a => coefficientJetAxisEquiv rowTypes I n z.1 a.val)) = _
  ring

include hu₀ in

theorem allocatedSupportedSliced_referenceCell_pos
    (hv₀ : ∀ j, IntegerScalarCube (principalAxisLength (fun a => ¬grid a)
      (allocatedPrincipalSides B U b S) j) (fun a => (v₀ j a : ℤ))) :
    0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
      (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)) := by
  have hu := containedSupportedProgressionAxisLaw_cube_support B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S)
    hH hsubset q r hcell grid u₀ hu₀
  exact principalResidueCell_pos_of_cube B (layerSamplerDegree I n) (allocatedPrincipalSides B U b S)
    (allocatedPrincipalSides_pos B U b S) q y₀
    (principalAxisJoin_cube B (layerSamplerDegree I n) (allocatedPrincipalSides B U b S) grid u₀ v₀ hu hv₀)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))

variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell grid
local notation "height" => (fun a : gridAxes => basisAxisScale (b (Sigma.fst (ig a))) (Sigma.snd (ig a)))

variable (x : G → IntegerScalarCubeBox α S.value)
variable (u₀ : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (hu₀ : ((containedSupportedProgressionAxisLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell (allocatedGridAxis (I := I) U b S.value))).weight u₀ ≠ 0)
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)] (d : ℕ) [NeZero d]
variable (hperiod : ∀ j, integerScalarLattice ((fun j : Fin m => {t : Finset α // t ∈ rowSets j}) j) (q : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) ((fun j => (Subtype.val : rowSets j → Finset α)) j)).mulVecLin.range)
local notation "root" u => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v₀)
local notation "dirs" u => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v₀)
local notation "residue" u:max => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v₀) q)

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "quarter" => (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "region" => mixedCoveredJetRegion (E := Q) U o b d quarter
local notation "y₀" => principalAxisJoin grid u₀ v₀
local notation "gridDensity" => allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q r hcell x

include hu₀ hperiod in

theorem allocatedSupportedSlicedProductProfile_chart_error
    (f : ((Σ a : {a // ¬grid a}, rowTypes a.val.1) → ℝ) → ℝ)
    (hfullcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
      (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
    (rad : ℝ≥0) (hrad : 0 < rad)
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α)) {ε : ℝ}
    (z : MixedCoveredJetSource I rowTypes Q n d) (hz : z ∈ region)
    (he : ‖(allocatedFullGridNaturalVolume B U b S rowSets : ℂ) *
        (gridDensity (allocatedFullGridRowsOfMixed B U b S rowSets z.1) : ℂ) -
        allocatedFullGridSiteApproximation B U b S rowSets e
          (allocatedFullGridRowsOfMixed B U b S rowSets z.1)‖ ≤ ε) :
    ‖allocatedProductSiteCutoff B U b S rowSets o hb bW d rad hrad (chart z) *
      ((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
        (principalAxisJoin grid u v₀) q f (chart z)) : ℂ) -
      allocatedProductFullGridProfile B U b S rowSets d rad hrad x hb o bW q y₀ f hR hσ hfullcell e (chart z)‖ ≤
    ‖allocatedProductFullGridPrefactor B U b S rowSets d rad hrad x hb o bW q y₀ f (chart z)‖ * ε := by
  rw [allocatedSupportedSlicedMaskedProfile_chart_mean B U b hR hσ S rowSets
    H step c hH hsubset q r hcell x u₀ hu₀ v₀ Q d hperiod hb o bW f z hz,
    allocatedProductFullGridProfile_mixed B U b S rowSets d rad hrad x hb o bW q y₀ f hR hσ hfullcell e z hz,
    Complex.ofReal_mul]
  let N : ℂ := (allocatedFullGridNaturalVolume B U b S rowSets : ℂ)
  have hN : N ≠ 0 := Complex.ofReal_ne_zero.mpr (allocatedFullGridNaturalVolume_pos B U b hR S rowSets).ne'
  have heq :
      allocatedProductSiteCutoff B U b S rowSets o hb bW d rad hrad (chart z) *
        ((gridDensity (allocatedFullGridRowsOfMixed B U b S rowSets z.1) : ℂ) *
          (allocatedWholeMaskedGridlessProfile B U b S x y₀ rows hb o bW d q f (chart z) : ℂ)) -
        allocatedProductFullGridPrefactor B U b S rowSets d rad hrad x hb o bW q y₀ f (chart z) *
          allocatedFullGridSiteApproximation B U b S rowSets e (allocatedFullGridRowsOfMixed B U b S rowSets z.1) =
      allocatedProductFullGridPrefactor B U b S rowSets d rad hrad x hb o bW q y₀ f (chart z) *
        (N * (gridDensity (allocatedFullGridRowsOfMixed B U b S rowSets z.1) : ℂ) -
          allocatedFullGridSiteApproximation B U b S rowSets e (allocatedFullGridRowsOfMixed B U b S rowSets z.1)) := by
    unfold allocatedProductFullGridPrefactor
    change _ - _ * (1 / N * _) * _ = (_ * (1 / N * _)) * (N * _ - _)
    field_simp
  rw [heq, norm_mul]
  exact mul_le_mul_of_nonneg_left he (norm_nonneg _)

include hu₀ hperiod in

theorem allocatedSupportedSlicedProductProfile_error
    (f : ((Σ a : {a // ¬grid a}, rowTypes a.val.1) → ℝ) → ℝ)
    (hfullcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
      (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
    (rad : ℝ≥0) (hrad : 0 < rad)
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α)) {ε : ℝ}
    (he : ∀ z : AllocatedFrozenJetRows B U b S rowTypes,
      ‖(allocatedFullGridNaturalVolume B U b S rowSets : ℂ) * (gridDensity z : ℂ) -
        allocatedFullGridSiteApproximation B U b S rowSets e z‖ ≤ ε)
    (y : EuclideanJetLayers U rowTypes) :
    ‖allocatedProductSiteCutoff B U b S rowSets o hb bW d rad hrad y *
      ((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
        (principalAxisJoin grid u v₀) q f y) : ℂ) -
      allocatedProductFullGridProfile B U b S rowSets d rad hrad x hb o bW q y₀ f hR hσ hfullcell e y‖ ≤
    ‖allocatedProductFullGridPrefactor B U b S rowSets d rad hrad x hb o bW q y₀ f y‖ * ε := by
  by_cases hy : y ∈ chart '' region
  · obtain ⟨z, hz, rfl⟩ := hy
    exact allocatedSupportedSlicedProductProfile_chart_error B U b hR hσ S rowSets H step c hH hsubset q r hcell
      x u₀ hu₀ v₀ Q d hperiod hb o bW f hfullcell rad hrad e z hz (he _)
  · have hzero (u) : allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
        (principalAxisJoin grid u v₀) q f y = 0 := by
      unfold allocatedWholeMaskedCoveredProfile allocatedCoveredProfileDensity
      exact restrictedChartDensity_zero _ _ _ _ hy
    simp only [hzero, FiniteProbabilityWeights.mean_const, Complex.ofReal_zero, mul_zero,
      allocatedProductFullGridProfile_zero B U b S rowSets d rad hrad x hb o bW q y₀ f hR hσ hfullcell e y hy,
      allocatedProductFullGridPrefactor_zero B U b S rowSets d rad hrad x hb o bW q y₀ f y hy,
      sub_zero, norm_zero, zero_mul, le_refl]

include hu₀ hperiod in

theorem allocatedSupportedSlicedProductProfile_combined_error
    (f : ((Σ a : {a // ¬grid a}, rowTypes a.val.1) → ℝ) → ℝ)
    (hfullcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
      (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
    (rad : ℝ≥0) (hrad : 0 < rad)
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α)) {ε η : ℝ}
    (he : ∀ z : AllocatedFrozenJetRows B U b S rowTypes,
      ‖(allocatedFullGridNaturalVolume B U b S rowSets : ℂ) * (gridDensity z : ℂ) -
        allocatedFullGridSiteApproximation B U b S rowSets e z‖ ≤ ε)
    {Nt V Cc Hs : gridAxes → ℝ} {L : ℝ≥0}
    (heb : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) L (Hs a))
    (F : EuclideanJetLayers U rowTypes → ℂ) (hη : 0 ≤ η)
    (hF : ∀ y, ‖allocatedProductFullGridPrefactor B U b S rowSets d rad hrad x hb o bW q y₀ f y - F y‖ ≤ η)
    (y : EuclideanJetLayers U rowTypes) :
    ‖allocatedProductSiteCutoff B U b S rowSets o hb bW d rad hrad y *
      ((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
        (principalAxisJoin grid u v₀) q f y) : ℂ) -
      F y * allocatedFullGridChartModel B U b S rowSets d hb o bW e y‖ ≤
    ‖allocatedProductFullGridPrefactor B U b S rowSets d rad hrad x hb o bW q y₀ f y‖ * ε + η * ∏ a, Cc a := by
  have hg := allocatedSupportedSlicedProductProfile_error B U b hR hσ S rowSets H step c hH hsubset q r hcell
    x u₀ hu₀ v₀ Q d hperiod hb o bW f hfullcell rad hrad e he y
  have hl := allocatedProductFullGridProfile_prefactor_error B U b S rowSets d rad hrad x hb o bW q y₀ f
    hR hσ hfullcell e heb F hη hF y
  have ht := dist_triangle
    (allocatedProductSiteCutoff B U b S rowSets o hb bW d rad hrad y *
      ((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
        (principalAxisJoin grid u v₀) q f y) : ℂ))
    (allocatedProductFullGridProfile B U b S rowSets d rad hrad x hb o bW q y₀ f hR hσ hfullcell e y)
    (F y * allocatedFullGridChartModel B U b S rowSets d hb o bW e y)
  simp only [dist_eq_norm] at ht
  exact ht.trans (add_le_add hg hl)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (rowSets : Fin m → Finset (Finset (Fin 1)))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin 1) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin 1)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin 1) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin 1) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
local notation "mask" => allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

variable (hperiod : ∀ j, integerScalarLattice {t : Finset (Fin 1) // t ∈ rowSets j} (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset (Fin 1) // t ∈ rowSets j} → Finset (Fin 1))).mulVecLin.range)
variable {M : ℝ} (hM : 1 ≤ M)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
  (fun j => (Subtype.val : {t : Finset (Fin 1) // t ∈ rowSets j} → Finset (Fin 1))) j q
  (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
    (fun j => (Subtype.val : {t : Finset (Fin 1) // t ∈ rowSets j} → Finset (Fin 1))) j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : {t : Finset (Fin 1) // t ∈ rowSets j} → Finset (Fin 1))) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : {t : Finset (Fin 1) // t ∈ rowSets j} → Finset (Fin 1))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ M)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin 1)) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

variable (hrows : ∀ j t, t ∈ rowSets j)
variable (hB : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, 4 ≤ Fintype.card (B a.val))
variable (lower width : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

variable (hσ : ∀ j, 0 < σ j)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin 1) → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := Fin 1) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = label)))
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell grid
variable (hu₀ : (containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell
  (allocatedGridAxis (I := I) U b S.value)).weight (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀) ≠ 0)
variable (hmodulus : ∀ j, integerScalarLattice {t : Finset (Fin 1) // t ∈ rowSets j} (q : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset (Fin 1) // t ∈ rowSets j} → Finset (Fin 1))).mulVecLin.range)
variable (hy₀ : ∀ j, IntegerScalarCube (allocatedPrincipalSides B U b S j) (fun a => (y₀ j a : ℤ)))
local notation "gridAxes" => {a // grid a}
local notation "gridDensity" => allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q label hcell x
local notation "ideal" => allocatedSlicedRowIdeal B U b S rowSets hR hrows hB lower width
local notation "prefactor" => allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ ideal

include hperiod hM hm hR hC hchart hbudget hu₀ hmodulus hy₀ in
theorem exists_allocated_supported_sliced_ideal_model
    (e : gridAxes → ScalarSiteExpansion.{0,0} (Finset (Fin 1)))
    {εgrid : ℝ}
    (he : ∀ z : AllocatedFrozenJetRows B U b S rowTypes,
      ‖(allocatedFullGridNaturalVolume B U b S rowSets : ℂ) * (gridDensity z : ℂ) -
        allocatedFullGridSiteApproximation B U b S rowSets e z‖ ≤ εgrid)
    {Nt V Cc Hs : gridAxes → ℝ} {Lg : ℝ≥0}
    (heb : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a))
    (O : ℕ) (hO : Fintype.card (OneCubeActiveRow grid) ≤ O)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    {a δ P ε : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hP : 0 ≤ P)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    (hε : 0 < ε) (hHP : (4 : ℝ) ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P) :
    let cutoffLip : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / 4
    let Q := slicedJointDensityLogBudget O m P + P
    let A := Real.exp ((2 * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q)
    let maskCap := M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period
    ∃ k : ℕ, (k : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      (Fintype.card (Finset (Fin 1) × LayerSamplerAxis I n → Fin k) : ℝ) ≤
        Real.exp ((2 * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8)) ∧
      ∃ (a : (Finset (Fin 1) × LayerSamplerAxis I n → Fin k) → ℂ)
        (f : (Finset (Fin 1) × LayerSamplerAxis I n → Fin k) → Finset (Fin 1) → (LayerSamplerAxis I n → ℝ) → ℂ),
        (∑ i, ‖a i‖) ≤ A ∧
        (∀ i s v, ‖f i s v‖ ≤ 1) ∧
        (∀ i s, LipschitzWith (⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ + cutoffLip) (f i s)) ∧
        (∀ i s v, (∃ j, (4 : ℝ) < |v j|) → f i s v = 0) ∧
        (∑ label : Finset (Fin 1) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ i,
          ‖allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i‖) ≤
          ‖inverseNormalizer‖ * ((Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ^ Fintype.card (Finset (Fin 1)) * maskCap * A) ∧
        (∀ label i s y,
          ‖allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label (f i s) y‖ ≤ 1) ∧
        (∀ label i s, Measurable (allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label (f i s))) ∧
        Measurable (allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f) ∧
        (∀ y : EuclideanJetLayers U rowTypes,
          ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀
              (allocatedSlicedRowIdeal B U b S rowSets hR hrows hB lower width) y -
            allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y‖ ≤
            ‖inverseNormalizer‖ * maskCap * ε) ∧
        ∀ y : EuclideanJetLayers U rowTypes,
          ‖cutoff y * ((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
              (principalAxisJoin grid u (principalAxisRestrict (fun a => ¬grid a) y₀)) q ideal y) : ℂ) -
            allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y *
              allocatedFullGridChartModel B U b S rowSets d hb o bW e y‖ ≤
            ‖prefactor y‖ * εgrid + (‖inverseNormalizer‖ * maskCap * ε) * ∏ a, Cc a := by
  intro cutoffLip Q A maskCap
  obtain ⟨k, hk, hcard, a, f, ha', hf, hLf, hs, hc, hfn, hfm, hmeas, herr⟩ :=
    exists_allocated_global_masked_sliced_approximation B U b S rowSets x y₀ q d period r hr hb o bW
      hperiod hM hm hR C hC hchart hbudget hrows hB lower width O hO hwidth
      ha hδ hP haP hδP hprincipal hw hl hε hHP hεP
  refine ⟨k, hk, hcard, a, f, ha', hf, hLf, hs, hc, hfn, hfm, hmeas, herr, ?_⟩
  have hfullcell := principalResidueCell_pos_of_cube B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S) q y₀ hy₀
  have hjoin := principalAxisJoin_restrict grid y₀
  intro y
  have hfullcell' : 0 < (principalTupleWeights (α := Fin 1) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
      (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q
        (principalAxisJoin grid (principalAxisRestrict grid y₀) (principalAxisRestrict (fun a => ¬grid a) y₀)))) := by
    simpa only [hjoin] using hfullcell
  have hlong : ∀ y, ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q
      (principalAxisJoin grid (principalAxisRestrict grid y₀) (principalAxisRestrict (fun a => ¬grid a) y₀)) ideal y -
      allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y‖ ≤
        ‖inverseNormalizer‖ * maskCap * ε := by simpa only [hjoin] using herr
  have hη : 0 ≤ ‖inverseNormalizer‖ * maskCap * ε := by
    have hmask : 0 ≤ maskCap := mul_nonneg (pow_nonneg (zero_le_one.trans hM) _) (coefficientDeckPeriodCap_nonneg rowTypes E period)
    exact mul_nonneg (mul_nonneg (norm_nonneg _) hmask) hε.le
  have h := allocatedSupportedSlicedProductProfile_combined_error B U b hR hσ S rowSets H step c hH hsubset q label hcell
    x (principalAxisRestrict grid y₀) hu₀ (principalAxisRestrict (fun a => ¬grid a) y₀) E d hmodulus hb o bW
    ideal hfullcell' r hr e he heb
    (allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f) hη hlong y
  simpa only [hjoin] using h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (rowSets : Fin m → Finset (Finset (Fin 1)))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin 1) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin 1)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin 1) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin 1) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
local notation "mask" => allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

variable (hperiod : ∀ j, integerScalarLattice {t : Finset (Fin 1) // t ∈ rowSets j} (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset (Fin 1) // t ∈ rowSets j} → Finset (Fin 1))).mulVecLin.range)
variable {M : ℝ} (hM : 1 ≤ M)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
  (fun j => (Subtype.val : {t : Finset (Fin 1) // t ∈ rowSets j} → Finset (Fin 1))) j q
  (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
    (fun j => (Subtype.val : {t : Finset (Fin 1) // t ∈ rowSets j} → Finset (Fin 1))) j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : {t : Finset (Fin 1) // t ∈ rowSets j} → Finset (Fin 1))) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : {t : Finset (Fin 1) // t ∈ rowSets j} → Finset (Fin 1))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ M)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin 1)) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

variable (hrows : ∀ j t, t ∈ rowSets j)
variable (hB : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, 4 ≤ Fintype.card (B a.val))
variable (lower width : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

variable (hσ : ∀ j, 0 < σ j)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin 1) → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := Fin 1) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = label)))
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell grid
variable (hu₀ : (containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell
  (allocatedGridAxis (I := I) U b S.value)).weight (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀) ≠ 0)
variable (hmodulus : ∀ j, integerScalarLattice {t : Finset (Fin 1) // t ∈ rowSets j} (q : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset (Fin 1) // t ∈ rowSets j} → Finset (Fin 1))).mulVecLin.range)
variable (hy₀ : ∀ j, IntegerScalarCube (allocatedPrincipalSides B U b S j) (fun a => (y₀ j a : ℤ)))
local notation "gridAxes" => {a // grid a}
local notation "gridDensity" => allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q label hcell x
local notation "ideal" => allocatedSlicedRowIdeal B U b S rowSets hR hrows hB lower width
local notation "prefactor" => allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ ideal

include hperiod hM hm hR hC hchart hbudget hu₀ hmodulus hy₀ in
theorem exists_allocated_supported_sliced_source_model
    (T : Fin m → ℝ) (hT : ∀ j, 0 ≤ T j) (h4 : ∀ j, 4 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card (Fin 1) * ((Fintype.card (Fin 1) : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j, (rowSets j).card * T j ≤ (r : ℝ)) (hσ1 : ∀ j, σ j ≤ 1)
    (e : gridAxes → ScalarSiteExpansion.{0,0} (Finset (Fin 1)))
    {εgrid : ℝ} (hεgrid : 0 ≤ εgrid)
    (he : ∀ z : AllocatedFrozenJetRows B U b S rowTypes,
      ‖(allocatedFullGridNaturalVolume B U b S rowSets : ℂ) * (gridDensity z : ℂ) -
        allocatedFullGridSiteApproximation B U b S rowSets e z‖ ≤ εgrid)
    {Nt V Cc Hs : gridAxes → ℝ} {Lg : ℝ≥0}
    (heb : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a))
    (O : ℕ) (hO : Fintype.card (OneCubeActiveRow grid) ≤ O)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    {a δ P ε : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hP : 0 ≤ P)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P)
    {Pcap : ℝ} (hPcap : 0 ≤ Pcap) (haPcap : a⁻¹ ≤ Real.exp Pcap) (hδPcap : δ⁻¹ ≤ Real.exp Pcap)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    (hε : 0 < ε) (hHP : (4 : ℝ) ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P) :
    let cutoffLip : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / 4
    let Q := slicedJointDensityLogBudget O m P + P
    let A := Real.exp ((2 * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q)
    let maskCap := M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period
    ∃ k : ℕ, (k : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      (Fintype.card (Finset (Fin 1) × LayerSamplerAxis I n → Fin k) : ℝ) ≤
        Real.exp ((2 * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8)) ∧
      ∃ (a : (Finset (Fin 1) × LayerSamplerAxis I n → Fin k) → ℂ)
        (f : (Finset (Fin 1) × LayerSamplerAxis I n → Fin k) → Finset (Fin 1) → (LayerSamplerAxis I n → ℝ) → ℂ),
        (∑ i, ‖a i‖) ≤ A ∧
        (∀ i s v, ‖f i s v‖ ≤ 1) ∧
        (∀ i s, LipschitzWith (⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ + cutoffLip) (f i s)) ∧
        (∀ i s v, (∃ j, (4 : ℝ) < |v j|) → f i s v = 0) ∧
        (∑ label : Finset (Fin 1) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ i,
          ‖allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i‖) ≤
          ‖inverseNormalizer‖ * ((Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ^ Fintype.card (Finset (Fin 1)) * maskCap * A) ∧
        (∀ label i s y,
          ‖allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label (f i s) y‖ ≤ 1) ∧
        (∀ label i s, Measurable (allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label (f i s))) ∧
        Measurable (allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f) ∧
        (∀ y : EuclideanJetLayers U rowTypes,
          ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀
              (allocatedSlicedRowIdeal B U b S rowSets hR hrows hB lower width) y -
            allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y‖ ≤
            ‖inverseNormalizer‖ * maskCap * ε) ∧
        ∀ y : EuclideanJetLayers U rowTypes,
          ‖((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
              (principalAxisJoin grid u (principalAxisRestrict (fun a => ¬grid a) y₀)) q ideal y) : ℂ) -
            allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y *
              allocatedFullGridChartModel B U b S rowSets d hb o bW e y‖ ≤
            ‖inverseNormalizer‖ * maskCap *
              (Real.exp (slicedJointDensityLogBudget O m Pcap) * εgrid + ε * ∏ a, Cc a) := by
  intro cutoffLip Q A maskCap
  obtain ⟨k, hk, hcard, a, f, ha', hf, hLf, hs, hc, hfn, hfm, hmeas, hlong, herr⟩ :=
    exists_allocated_supported_sliced_ideal_model B U b S rowSets x y₀ q d period r hr hb o bW
      hperiod hM hm hR C hC hchart hbudget hrows hB lower width hσ H step c hH hsubset label hcell
      hu₀ hmodulus hy₀ e he heb O hO hwidth ha hδ hP haP hδP hprincipal hw hl hε hHP hεP
  refine ⟨k, hk, hcard, a, f, ha', hf, hLf, hs, hc, hfn, hfm, hmeas, hlong, ?_⟩
  have hb0 (j : Fin m) : C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4 := by
    have hb := hbudget j
    have hcard : (Fintype.card (Finset (Fin 1)) : ℝ) = 2 := by norm_num
    rw [hcard] at hb
    have hn := Nat.cast_nonneg (α := ℝ) (rowSets j).card
    have hp : 0 ≤ C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) :=
      mul_nonneg (hC j) (mul_nonneg (by positivity) (mul_nonneg (by positivity) (hR j).le))
    nlinarith only [hb, hn, hp]
  intro y
  have hfix := allocatedSlicedRowIdeal_cutoff_fixes_mean B U b S rowSets o hb bW d r hr hR hσ T hT hsource hradius C hC hchart hb0
    hσ1 h4 hrows hB lower width hwidth ha hδ hprincipal hw hl x gridLaw
    (fun u => principalAxisJoin grid u (principalAxisRestrict (fun a => ¬grid a) y₀)) q y
  have h := herr y
  rw [hfix] at h
  have hc := allocatedSlicedProductPrefactor_cap B U b S rowSets x y₀ q d period r hr hb o bW
    hperiod hM hm hR C hC hchart hbudget hrows hB lower width O hO
    ha hδ hPcap haPcap hδPcap hprincipal hw hl y
  calc
    _ ≤ ‖prefactor y‖ * εgrid + (‖inverseNormalizer‖ * maskCap * ε) * ∏ a, Cc a := h
    _ ≤ (‖inverseNormalizer‖ * maskCap * Real.exp (slicedJointDensityLogBudget O m Pcap)) * εgrid +
        (‖inverseNormalizer‖ * maskCap * ε) * ∏ a, Cc a :=
      add_le_add (mul_le_mul_of_nonneg_right hc hεgrid) le_rfl
    _ = _ := by ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (rowSets : Fin m → Finset (Finset (Fin 1)))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin 1) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin 1)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin 1)) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

variable (hrows : ∀ j t, t ∈ rowSets j)
variable (hB : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, 4 ≤ Fintype.card (B a.val))
variable (lower width : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

variable (hσ : ∀ j, 0 < σ j)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin 1) → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := Fin 1) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = label)))
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell grid
local notation "gridAxes" => {a // grid a}
local notation "ideal" => allocatedSlicedRowIdeal B U b S rowSets hR hrows hB lower width

include hR hC hchart hbudget in

theorem exists_allocated_supported_sliced_uniform_source_model
    (hq : 0 < q) {δg : ℝ} (hδg : 0 < δg)
    (hdenseg : ∀ tg, δg * allocatedPrincipalSides B U b S tg ≤ (H tg : ℝ))
    (Tg : ℕ) (hQTg : (((Fintype.card (Fin 1) + 1) * q : ℕ) : ℝ) / δg ≤ Tg)
    (hstep : ∀ tg, 0 < step tg)
    (Ag : ℝ≥0) (hAg : LipschitzWith Ag Real.smoothTransition) (Pg : ℝ) (hPg : 1 ≤ Pg)
    (hcP : scalarCubePrimitiveEnvelope Empty Ag 16 (128 * probabilityProfileLipschitz) 1 ≤ Pg)
    (hsP : scalarCubePrimitiveEnvelope (Fin 1) Ag 1 0 q ≤ Pg)
    (hstride : ∀ tg, ((step tg * q : ℕ) : ℝ) ≤ Pg)
    (hrowDegree : ∀ j tg, tg ∈ rowSets j → tg.card ≤ j.val + 1)
    (hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val (rowSets j).card
      ((layerTailDegree m + 1) * (rowSets j).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : ∀ j i, uniformSpectrumBlockCount j.val (rowSets j).card
      ((j.val + 1) * (rowSets j).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    {Dg vg wg tg pg Eg εgrid : ℝ}
    (hDg : 0 ≤ Dg) (hvg : 0 ≤ vg) (hwg : 0 ≤ wg) (htg : 0 ≤ tg) (hpg : 0 ≤ pg) (hEg : 0 ≤ Eg)
    (hcube : (Fintype.card (Fin 1) : ℝ) ≤ Dg) (hdegree : ∀ j : Fin m, ((j.val + 1 : ℕ) : ℝ) ≤ Dg)
    (hrowsD : ∀ j, ((rowSets j).card : ℝ) ≤ Dg)
    (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ Dg)
    (hblocks : ∀ j i, (Fintype.card (B ⟨j, Sum.inr i⟩) : ℝ) ≤ Dg)
    (hRv : ∀ j, R j ≤ Real.exp vg) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp vg)
    (hδw : δg⁻¹ ≤ Real.exp wg) (hTg : (Tg : ℝ) ≤ Real.exp tg)
    (hcoeff : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp vg)
    (hPp₀ : Pg ≤ Real.exp pg) (haxes : (Fintype.card gridAxes : ℝ) ≤ Dg)
    (hεgrid : 0 < εgrid) (hεgridEg : εgrid⁻¹ ≤ Real.exp Eg) (hσgrid : ∀ j, σ j ≤ 1)
    (T : Fin m → ℝ) (hT : ∀ j, 0 ≤ T j) (h4 : ∀ j, 4 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card (Fin 1) * ((Fintype.card (Fin 1) : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j, (rowSets j).card * T j ≤ (r : ℝ)) (hσ1 : ∀ j, σ j ≤ 1)
    (O : ℕ) (hO : Fintype.card (OneCubeActiveRow grid) ≤ O)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    {a δ P ε : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hP : 0 ≤ P)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P)
    {Pcap : ℝ} (hPcap : 0 ≤ Pcap) (haPcap : a⁻¹ ≤ Real.exp Pcap) (hδPcap : δ⁻¹ ≤ Real.exp Pcap)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    (hε : 0 < ε) (hHP : (4 : ℝ) ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P) :
    let p := slicedGridGeometryLog Dg vg wg tg + pg
    let L := fun j : Fin m => fun e : ℝ => slicedGridSiteLog j.val (rowSets j).card
      ((layerTailDegree m + 1) * (rowSets j).card) ((j.val + 1) * (rowSets j).card) Dg p e
    let Cp := ∑ j, (L j 0 + Dg * (vg + 1))
    let Eg' := uniformProductAccuracyLog Dg Cp Eg + Dg * (vg + 1) + 1
    let Op := ∑ j, (siteExponentialOutputLog (Fintype.card (Finset (Fin 1))) (L j Eg') + (Dg + 1) * (vg + 1))
    ∃ e : gridAxes → ScalarSiteExpansion.{0,0} (Finset (Fin 1)),
      (∀ a, (e a).Bounds (Real.exp Op) (Real.exp Op) (Real.exp Op)
        ⟨Real.exp Op, Real.exp_nonneg _⟩ (Real.exp (slicedGridGeometryLog Dg vg wg tg + (Dg + vg + 8)))) ∧
      ∀ (x : G → IntegerScalarCubeBox (Fin 1) S.value)
        (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin 1) (allocatedPrincipalSides B U b S))
        (_hperiod : ∀ j, integerScalarLattice {t : Finset (Fin 1) // t ∈ rowSets j} (period : ℤ) ≤
          (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset (Fin 1) // t ∈ rowSets j} → Finset (Fin 1))).mulVecLin.range)
        {M : ℝ} (_hM : 1 ≤ M)
        (_hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
          (fun j => (Subtype.val : {t : Finset (Fin 1) // t ∈ rowSets j} → Finset (Fin 1))) j q
          (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
            (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
            (fun j => (Subtype.val : {t : Finset (Fin 1) // t ∈ rowSets j} → Finset (Fin 1))) j
            (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
          allocatedIntegerKernelMask B U b S x
            (fun j => (Subtype.val : {t : Finset (Fin 1) // t ∈ rowSets j} → Finset (Fin 1))) j q
            (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
              (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
              (fun j => (Subtype.val : {t : Finset (Fin 1) // t ∈ rowSets j} → Finset (Fin 1))) j
              (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ M)

        (_hu₀ : (containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
          (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell
          (allocatedGridAxis (I := I) U b S.value)).weight (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀) ≠ 0)
        (_hmodulus : ∀ j, integerScalarLattice {t : Finset (Fin 1) // t ∈ rowSets j} (q : ℤ) ≤
          (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset (Fin 1) // t ∈ rowSets j} → Finset (Fin 1))).mulVecLin.range)
        (_hy₀ : ∀ j, IntegerScalarCube (allocatedPrincipalSides B U b S j) (fun a => (y₀ j a : ℤ))),
    let cutoffLip : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / 4
    let Q := slicedJointDensityLogBudget O m P + P
    let A := Real.exp ((2 * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q)
    let maskCap := M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period
    ∃ k : ℕ, (k : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      (Fintype.card (Finset (Fin 1) × LayerSamplerAxis I n → Fin k) : ℝ) ≤
        Real.exp ((2 * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8)) ∧
      ∃ (a : (Finset (Fin 1) × LayerSamplerAxis I n → Fin k) → ℂ)
        (f : (Finset (Fin 1) × LayerSamplerAxis I n → Fin k) → Finset (Fin 1) → (LayerSamplerAxis I n → ℝ) → ℂ),
        (∑ i, ‖a i‖) ≤ A ∧
        (∀ i s v, ‖f i s v‖ ≤ 1) ∧
        (∀ i s, LipschitzWith (⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ + cutoffLip) (f i s)) ∧
        (∀ i s v, (∃ j, (4 : ℝ) < |v j|) → f i s v = 0) ∧
        (∑ label : Finset (Fin 1) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ i,
          ‖allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i‖) ≤
          ‖inverseNormalizer‖ * ((Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ^ Fintype.card (Finset (Fin 1)) * maskCap * A) ∧
        (∀ label i s y,
          ‖allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label (f i s) y‖ ≤ 1) ∧
        (∀ label i s, Measurable (allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label (f i s))) ∧
        Measurable (allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f) ∧
        (∀ y : EuclideanJetLayers U rowTypes,
          ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀
              (allocatedSlicedRowIdeal B U b S rowSets hR hrows hB lower width) y -
            allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y‖ ≤
            ‖inverseNormalizer‖ * maskCap * ε) ∧
        (∀ y : EuclideanJetLayers U rowTypes,
          ‖((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
              (principalAxisJoin grid u (principalAxisRestrict (fun a => ¬grid a) y₀)) q ideal y) : ℂ) -
            allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y *
              allocatedFullGridChartModel B U b S rowSets d hb o bW e y‖ ≤
            ‖inverseNormalizer‖ * maskCap *
              (Real.exp (slicedJointDensityLogBudget O m Pcap) * εgrid + ε * ∏ _a : gridAxes, Real.exp Op)) ∧
        ∀ (μ : Measure (EuclideanJetLayers U rowTypes)) [IsProbabilityMeasure μ]
          (φ : EuclideanJetLayers U rowTypes → ℂ), Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
          Integrable (fun y => ((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile
            B U b hR hσ S x rows hb o bW d
              (principalAxisJoin grid u (principalAxisRestrict (fun a => ¬grid a) y₀)) q
                (allocatedSlicedRowIdeal B U b S rowSets hR hrows hB lower width) y) : ℂ)) μ ∧
          ‖(∫ y, ((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile
              B U b hR hσ S x rows hb o bW d
                (principalAxisJoin grid u (principalAxisRestrict (fun a => ¬grid a) y₀)) q
                  (allocatedSlicedRowIdeal B U b S rowSets hR hrows hB lower width) y) : ℂ) * φ y ∂μ) -
            ∫ y, (allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y *
              allocatedFullGridChartModel B U b S rowSets d hb o bW e y) * φ y ∂μ‖ ≤
            ‖inverseNormalizer‖ * maskCap *
              (Real.exp (slicedJointDensityLogBudget O m Pcap) * εgrid +
                ε * ∏ _a : gridAxes, Real.exp Op) := by
  intro p L Cp E' Op
  obtain ⟨e, heb, he⟩ := exists_allocatedSupportedSliced_full_grid_site_expansion B U b hR hσ S
    rowSets H step c hH hsubset q label hcell hq hδg hdenseg Tg hQTg hstep Ag hAg Pg hPg
    hcP hsP hstride hrowDegree hBa hBi hDg hvg hwg htg hpg hEg hcube hdegree hrowsD htail hblocks
    hRv hRi hδw hTg hcoeff hPp₀ haxes hεgrid hεgridEg hσgrid
  refine ⟨e, heb, ?_⟩
  intro x y₀ hperiod M hM hm hu₀ hmodulus hy₀
  obtain ⟨k, hk, hcard, a₀, f, ha₀, hf, hLf, hs, hc, hfn, hfm, hmeas, hlong, herr⟩ :=
    exists_allocated_supported_sliced_source_model B U b S rowSets x y₀ q d period r hr hb o bW
    hperiod hM hm hR C hC hchart hbudget hrows hB lower width hσ H step c hH hsubset label hcell
    hu₀ hmodulus hy₀ T hT h4 hsource hradius hσ1 e hεgrid.le (he x) heb
    O hO hwidth ha hδ hP haP hδP hPcap haPcap hδPcap hprincipal hw hl hε hHP hεP

  refine ⟨k, hk, hcard, a₀, f, ha₀, hf, hLf, hs, hc, hfn, hfm, hmeas, hlong, herr, ?_⟩
  intro μ hμ φ hφ hφb
  exact allocatedFiniteSourceModel_test_error B U b S rowSets x y₀ q d period r hr hb o bW μ
    a₀ f hLf hf e heb _
    (allocatedWholeMaskedSlicedProfile_mean_measurable B U b hR hσ S rowSets hrows x
      hb o bW d hB lower width gridLaw
        (fun u => principalAxisJoin grid u (principalAxisRestrict (fun a => ¬grid a) y₀)) q)
    herr φ hφ hφb

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

private theorem oneCubeAllRows (m : ℕ) :
    ∀ (j : Fin m) (t : Finset (Fin 1)), t ∈ boundedBooleanJetRows (Fin 1) (j.val + 1) := by
  intro j t
  rw [boundedBooleanJetRows_oneCube (j.val + 1) (by omega)]
  exact Finset.mem_univ t

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal
attribute [local instance] ScalarSiteExpansion.termFinite

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin 1) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin 1) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin 1)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j : Fin m, ((boundedBooleanJetRows (Fin 1) (j.val + 1)).card + 1 : ℝ) * (Fintype.card (Finset (Fin 1)) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

variable (hB : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, 4 ≤ Fintype.card (B a.val))
variable (lower width : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

variable (hσ : ∀ j, 0 < σ j)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin 1) → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := Fin 1) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = label)))
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell grid
local notation "gridAxes" => {a // grid a}
local notation "ideal" => allocatedSlicedRowIdeal B U b S rowSets hR (oneCubeAllRows m) hB lower width

include hR hC hchart hbudget in
theorem exists_allocated_supported_sliced_uniform_physical_source
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (Qgrid : ℝ≥0) (hQgrid : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a},
      8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
        (allocatedGridIntegerAxis B U b S a).1 (allocatedGridIntegerAxis B U b S a).2) : ℝ) + 1) ≤ Qgrid)
    (hq : 0 < q) {δg : ℝ} (hδg : 0 < δg)
    (hdenseg : ∀ tg, δg * allocatedPrincipalSides B U b S tg ≤ (H tg : ℝ))
    (Tg : ℕ) (hQTg : (((Fintype.card (Fin 1) + 1) * q : ℕ) : ℝ) / δg ≤ Tg)
    (hstep : ∀ tg, 0 < step tg)
    (Ag : ℝ≥0) (hAg : LipschitzWith Ag Real.smoothTransition) (Pg : ℝ) (hPg : 1 ≤ Pg)
    (hcP : scalarCubePrimitiveEnvelope Empty Ag 16 (128 * probabilityProfileLipschitz) 1 ≤ Pg)
    (hsP : scalarCubePrimitiveEnvelope (Fin 1) Ag 1 0 q ≤ Pg)
    (hstride : ∀ tg, ((step tg * q : ℕ) : ℝ) ≤ Pg)
    (hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val (rowSets j).card
      ((layerTailDegree m + 1) * (rowSets j).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : ∀ j i, uniformSpectrumBlockCount j.val (rowSets j).card
      ((j.val + 1) * (rowSets j).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    {Dg vg wg tg pg Eg εgrid : ℝ}
    (hDg : 0 ≤ Dg) (hvg : 0 ≤ vg) (hwg : 0 ≤ wg) (htg : 0 ≤ tg) (hpg : 0 ≤ pg) (hEg : 0 ≤ Eg)
    (hcube : (Fintype.card (Fin 1) : ℝ) ≤ Dg) (hdegree : ∀ j : Fin m, ((j.val + 1 : ℕ) : ℝ) ≤ Dg)
    (hrowsD : ∀ j, ((rowSets j).card : ℝ) ≤ Dg)
    (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ Dg)
    (hblocks : ∀ j i, (Fintype.card (B ⟨j, Sum.inr i⟩) : ℝ) ≤ Dg)
    (hRv : ∀ j, R j ≤ Real.exp vg) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp vg)
    (hδw : δg⁻¹ ≤ Real.exp wg) (hTg : (Tg : ℝ) ≤ Real.exp tg)
    (hcoeff : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp vg)
    (hPp₀ : Pg ≤ Real.exp pg) (haxes : (Fintype.card gridAxes : ℝ) ≤ Dg)
    (hεgrid : 0 < εgrid) (hεgridEg : εgrid⁻¹ ≤ Real.exp Eg) (hσgrid : ∀ j, σ j ≤ 1)
    (T : Fin m → ℝ) (hT : ∀ j, 0 ≤ T j) (h4 : ∀ j, 4 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card (Fin 1) * ((Fintype.card (Fin 1) : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j, (rowSets j).card * T j ≤ (r : ℝ)) (hσ1 : ∀ j, σ j ≤ 1)
    (O : ℕ) (hO : Fintype.card (OneCubeActiveRow grid) ≤ O)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    {a δ P ε : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hP : 0 ≤ P)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P)
    {Pcap : ℝ} (hPcap : 0 ≤ Pcap) (haPcap : a⁻¹ ≤ Real.exp Pcap) (hδPcap : δ⁻¹ ≤ Real.exp Pcap)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    (hε : 0 < ε) (hHP : (4 : ℝ) ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P) :
    let p := slicedGridGeometryLog Dg vg wg tg + pg
    let L := fun j : Fin m => fun e : ℝ => slicedGridSiteLog j.val (rowSets j).card
      ((layerTailDegree m + 1) * (rowSets j).card) ((j.val + 1) * (rowSets j).card) Dg p e
    let Cp := ∑ j, (L j 0 + Dg * (vg + 1))
    let Eg' := uniformProductAccuracyLog Dg Cp Eg + Dg * (vg + 1) + 1
    let Op := ∑ j, (siteExponentialOutputLog (Fintype.card (Finset (Fin 1))) (L j Eg') + (Dg + 1) * (vg + 1))
    ∃ e : gridAxes → ScalarSiteExpansion.{0,0} (Finset (Fin 1)),
      (∀ a, (e a).Bounds (Real.exp Op) (Real.exp Op) (Real.exp Op)
        ⟨Real.exp Op, Real.exp_nonneg _⟩ (Real.exp (slicedGridGeometryLog Dg vg wg tg + (Dg + vg + 8)))) ∧
      ∀ (x : G → IntegerScalarCubeBox (Fin 1) S.value)
        (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin 1) (allocatedPrincipalSides B U b S))
        (d period : ℕ) [NeZero d] [NeZero period] (_hdiv : period ∣ d)
        (_hperiod : ∀ j, integerScalarLattice {t : Finset (Fin 1) // t ∈ rowSets j} (period : ℤ) ≤
          (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset (Fin 1) // t ∈ rowSets j} → Finset (Fin 1))).mulVecLin.range)
        {M : ℝ} (_hM : 1 ≤ M)
        (_hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
          (fun j => (Subtype.val : {t : Finset (Fin 1) // t ∈ rowSets j} → Finset (Fin 1))) j q
          (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
            (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
            (fun j => (Subtype.val : {t : Finset (Fin 1) // t ∈ rowSets j} → Finset (Fin 1))) j
            (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
          allocatedIntegerKernelMask B U b S x
            (fun j => (Subtype.val : {t : Finset (Fin 1) // t ∈ rowSets j} → Finset (Fin 1))) j q
            (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
              (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
              (fun j => (Subtype.val : {t : Finset (Fin 1) // t ∈ rowSets j} → Finset (Fin 1))) j
              (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ M)

        (_hu₀ : (containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
          (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell
          (allocatedGridAxis (I := I) U b S.value)).weight (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀) ≠ 0)
        (_hmodulus : ∀ j, integerScalarLattice {t : Finset (Fin 1) // t ∈ rowSets j} (q : ℤ) ≤
          (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset (Fin 1) // t ∈ rowSets j} → Finset (Fin 1))).mulVecLin.range)
        (_hy₀ : ∀ j, IntegerScalarCube (allocatedPrincipalSides B U b S j) (fun a => (y₀ j a : ℤ))),
    let cutoffLip : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / 4
    let Q := slicedJointDensityLogBudget O m P + P
    let A := Real.exp ((2 * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q)
    let maskCap := M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period
    ∃ k : ℕ, (k : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      (Fintype.card (Finset (Fin 1) × LayerSamplerAxis I n → Fin k) : ℝ) ≤
        Real.exp ((2 * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8)) ∧
      ∃ (a : (Finset (Fin 1) × LayerSamplerAxis I n → Fin k) → ℂ)
        (f : (Finset (Fin 1) × LayerSamplerAxis I n → Fin k) → Finset (Fin 1) → (LayerSamplerAxis I n → ℝ) → ℂ),
        (∑ i, ‖a i‖) ≤ A ∧
        (∀ i s v, ‖f i s v‖ ≤ 1) ∧
        (∀ i s, LipschitzWith (⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ + cutoffLip) (f i s)) ∧
        (∀ i s v, (∃ j, (4 : ℝ) < |v j|) → f i s v = 0) ∧
        (∑ label : Finset (Fin 1) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ i,
          ‖allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i‖) ≤
          ‖inverseNormalizer‖ * ((Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ^ Fintype.card (Finset (Fin 1)) * maskCap * A) ∧
        (∀ label i s y,
          ‖allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label (f i s) y‖ ≤ 1) ∧
        (∀ label i s, Measurable (allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label (f i s))) ∧
        Measurable (allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f) ∧
        (∀ y : EuclideanJetLayers U rowTypes,
          ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀
              (allocatedSlicedRowIdeal B U b S rowSets hR (oneCubeAllRows m) hB lower width) y -
            allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y‖ ≤
            ‖inverseNormalizer‖ * maskCap * ε) ∧
        (∀ y : EuclideanJetLayers U rowTypes,
          ‖((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
              (principalAxisJoin grid u (principalAxisRestrict (fun a => ¬grid a) y₀)) q ideal y) : ℂ) -
            allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y *
              allocatedFullGridChartModel B U b S rowSets d hb o bW e y‖ ≤
            ‖inverseNormalizer‖ * maskCap *
              (Real.exp (slicedJointDensityLogBudget O m Pcap) * εgrid + ε * ∏ _a : gridAxes, Real.exp Op)) ∧
        ∀ {X : Type*} (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
          (hm : ∀ j e, coefficients (poly j) e ∈ U j),
          let Lcoord : ℝ≥0 := K * ∑ j, Cforward j * Fintype.card (J j)
          let Llong : ℝ≥0 := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) * Lcoord +
            max ((⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ + cutoffLip) * Lcoord * period) (4 * period)
          let Lprimitive : ℝ≥0 := ⟨Real.exp Op, Real.exp_nonneg Op⟩
          let Lgrid : ℝ≥0 := max ((((Fintype.card gridAxes : ℝ≥0) * Lprimitive) * Qgrid) *
            Lcoord * Lprimitive ^ Fintype.card gridAxes) (4 * Lprimitive ^ Fintype.card gridAxes)
          ∃ g : (Finset (Fin 1) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) →
              (Finset (Fin 1) × LayerSamplerAxis I n → Fin k) → (∀ a, (e a).Term) → Finset (Fin 1) →
              (((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle)) ×
                ((Σ j, J j) → UnitAddCircle)) → ℂ,
            (∀ label i kg t, LipschitzWith (Llong + Lgrid) (g label i kg t)) ∧
            (∀ label i kg t z, ‖g label i kg t z‖ ≤ 1) ∧
            AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f poly hm g := by
  intro p L Cp E' Op
  have hrowDegree : ∀ (j : Fin m) (tg : Finset (Fin 1)),
      tg ∈ boundedBooleanJetRows (Fin 1) (j.val + 1) → tg.card ≤ j.val + 1 := by
    intro j tg htg
    exact (mem_boundedBooleanJetRows (j.val + 1) tg).mp htg
  obtain ⟨e, heb, he⟩ := exists_allocatedSupportedSliced_full_grid_site_expansion B U b hR hσ S
    rowSets H step c hH hsubset q label hcell hq hδg hdenseg Tg hQTg hstep Ag hAg Pg hPg
    hcP hsP hstride hrowDegree hBa hBi hDg hvg hwg htg hpg hEg hcube hdegree hrowsD htail hblocks
    hRv hRi hδw hTg hcoeff hPp₀ haxes hεgrid hεgridEg hσgrid
  refine ⟨e, heb, ?_⟩
  intro x y₀ d period hd hper hdiv hperiod M hM hm hu₀ hmodulus hy₀
  obtain ⟨k, hk, hcard, a₀, f, ha₀, hf, hLf, hs, hc, hfn, hfm, hmeas, hlong, herr⟩ :=
    exists_allocated_supported_sliced_source_model B U b S rowSets x y₀ q d period r hr hb o bW
      hperiod hM hm hR C hC hchart hbudget (oneCubeAllRows m) hB lower width hσ H step c hH hsubset label hcell
      hu₀ hmodulus hy₀ T hT h4 hsource hradius hσ1 e hεgrid.le (he x) heb
      O hO hwidth ha hδ hP haP hδP hPcap haPcap hδPcap hprincipal hw hl hε hHP hεP
  refine ⟨k, hk, hcard, a₀, f, ha₀, hf, hLf, hs, hc, hfn, hfm, hmeas, hlong, herr, ?_⟩
  intro X poly hp hm
  exact exists_allocated_finite_model_uniform_physical_expansion B U b S x y₀ q d period r hr hb o bW e
    hdiv hR C hC hchart hbudget Cforward hforward K hK a₀ f hLf hf heb Qgrid hQgrid poly hp hm
    (period : ℝ≥0) ⟨Real.exp Op, Real.exp_nonneg Op⟩ le_rfl (fun _ => le_rfl)

end Erdos3.VectorPolynomial

end

end OAI
