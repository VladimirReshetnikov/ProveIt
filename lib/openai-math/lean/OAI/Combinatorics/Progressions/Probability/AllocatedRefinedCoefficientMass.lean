import OAI.Combinatorics.Progressions.Geometry.AllocatedAmbientBoxTests
import OAI.Combinatorics.Progressions.Sampling.AllocatedFullGridCoefficientBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

theorem finiteTripleCoefficientMass_le
    {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    {a : A → ℂ} {b : B → ℂ} {c : C → D → ℂ} {S G I : ℝ}
    (ha : (∑ x, ‖a x‖) ≤ S) (hb : (∑ x, ‖b x‖) ≤ G)
    (hc : (∑ x, ∑ y, ‖c x y‖) ≤ I) :
    (∑ t : A × B, ∑ x, ∑ y, ‖(a t.1 * b t.2) * c x y‖) ≤ S * G * I := by
  have ha0 : 0 ≤ ∑ x, ‖a x‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hb0 : 0 ≤ ∑ x, ‖b x‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hc0 : 0 ≤ ∑ x, ∑ y, ‖c x y‖ :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  simp only [Fintype.sum_prod_type, norm_mul, ← Finset.mul_sum, ← Finset.sum_mul]
  exact mul_le_mul (mul_le_mul ha hb hb0 (ha0.trans ha)) hc hc0
    (mul_nonneg (ha0.trans ha) (hb0.trans hb))

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (coverWitness : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S (residueRefinedPeriod modulus q) r.val)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (hR : ∀ j, 0 < R j)
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ : ℝ} (hW : 0 ≤ W)
variable (period : ℕ) [NeZero period]

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => {s : Finset (Fin dim) // s ∈ rowSets j})
local notation "tuples" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S)
local notation "refined" => residueRefinedPeriod modulus q
local notation "positive" => AllocatedPositiveResidue (dim := dim) B U b S refined
local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "law" => FiniteProbabilityWeights.fiberLaw
  (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)) (principalResidueLabel refined)

variable (F : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
  (allocatedPrincipalSides B U b S) → AllocatedFiniteIdealData (Fin dim) I n)

noncomputable def allocatedConstructedSpatialCoefficientAt (mesh volume : ℝ)
    (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) : ℝ :=
  let data : AllocatedFiniteIdealData (Fin dim) I n := F ((coverWitness r).representative)
  ∑ t : (X → SpatialSiteLabel (Fin dim) modulus 4 mesh) ×
      (∀ a, ((coverWitness r).expansion a).Term),
    ∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period)),
      ∑ i : data.Term,
        ‖((allocatedSpatialExpansionCoefficient B U b S x X hM selection hx modulus hW mesh
            (principalResidueLabel modulus (wholeReference r.val)) t.1 / (volume : ℂ)) *
          coverSiteCoefficient (coverWitness r).expansion t.2) *
          allocatedProductMaskedIdealCoefficient B U b S rowSets x ((coverWitness r).representative)
            refined d period data.coefficient label i‖

theorem allocatedConstructedSpatialCoefficient_pre_bound
    {δ : ℝ≥0} {ε pI p0 E0 D O : ℝ}
    (hF : ∀ y₀ : tuples, (F y₀).Bounds B U b S rowSets x y₀ refined d period
      hb o bW hR δ ε pI (layerKernelIndexBound m M))
    {T C H : gridAxes → ℝ} {L : ℝ≥0}
    (hgrid : ∀ (r : positive) (a : gridAxes), ((coverWitness r).expansion a).Bounds (T a) (C a) (Real.exp O) L (H a))
    (hpI : 0 ≤ pI) (hp0 : 0 ≤ p0) (hE0 : 0 ≤ E0) (hO : 0 ≤ O)
    (hgeom : AllocatedComparisonDimensions (G := G) B (Fin dim) rowTypes D)
    (hn : ∀ j, (n j : ℝ) ≤ D) (hKcov : ∀ j, (Fintype.card (Kcov j) : ℝ) ≤ D)
    (hdim : dim ≤ m + 1) (hG : (Fintype.card G : ℝ) ≤ p0) (hX : (Fintype.card X : ℝ) ≤ p0)
    (hMP : (M : ℝ) ≤ Real.exp p0) (hmod : modulus ≤ M ^ (m + 1))
    (hperiodM : period ≤ M ^ (m + 1))
    (hq : ∀ z, 0 < q z) (hN : ∀ z, 0 < N z) (hτ : 0 < τ)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection)) :
    let mesh : ℝ := allocatedEarlyRecenteredMesh X selection M modulus p0 E0
    let volume : ℝ := ∏ z, ∏ i, physicalSpatialOutputScale (Fin dim)
      (trimmedSpatialRootScale τ N q z) (trimmedSpatialSlopeScale W τ N q z) S.value i
    let cost : ℝ := coarseSpatialPartitionLog (allocatedEarlyCoarseInput m dim (p0 + E0)) +
      allocatedFullGridCoefficientPreLog m D O +
      allocatedFiniteIdealMaskedLog m D pI ((m * 2 ^ (m + 1) : ℕ) * p0) ((m + 1 : ℕ) * p0)
    let cap : ℝ := ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖ * Real.exp cost / volume
    let mass := allocatedConstructedSpatialCoefficientAt (Kcov := Kcov)
      B U b S X modulus q wholeReference coverWitness d x hM selection hx hW period F mesh volume
    (∀ r, mass r ≤ cap) ∧
      (law).mean (fun r => if hr : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
          (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
          (Finset.univ.filter (fun y => principalResidueLabel refined y = r))
        then mass ⟨r, hr⟩ else 0) ≤ cap := by
  intro mesh volume cost cap mass
  rcases hgeom with ⟨hD, hdegree, _, hcube, haxes, _, _, hout, hrows, _, hprofile⟩
  have hscales (z : X) : 0 < trimmedSpatialRootScale τ N q z ∧
      0 < trimmedSpatialSlopeScale W τ N q z := trimmedSpatial_scales_pos hW hτ N q z (hN z) (hq z)
  have hvolume : 0 < volume := Finset.prod_pos (fun z _ => Finset.prod_pos (fun i _ =>
    physicalSpatialOutputScale_pos (Fin dim) (hscales z).1 (hscales z).2 (Nat.cast_pos.mpr S.positive) i))
  have hcost := allocatedEarlyRecenteredMesh_partition_budget m X selection hp0 hE0 hG hX hM hMP hmod
  have hgridCost := (allocatedFullGrid_coefficient_pre_bound B U b S refined coverWitness
    hgrid hO hdim haxes).1
  have hperiodExp : (period : ℝ) ≤ Real.exp ((m + 1 : ℕ) * p0) := by
    calc
      _ ≤ (M : ℝ) ^ (m + 1) := by exact_mod_cast hperiodM
      _ ≤ (Real.exp p0) ^ (m + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hMP _
      _ = _ := (Real.exp_nat_mul p0 (m + 1)).symm
  have hideal (r : positive) := allocatedFiniteIdeal_masked_coefficient_budget
    B U b S rowSets x ((coverWitness r).representative) refined d period hb o bW hR
    (F ((coverWitness r).representative)) (hF ((coverWitness r).representative))
    hpI hD (by positivity : 0 ≤ (m * 2 ^ (m + 1) : ℕ) * p0)
    (by positivity : 0 ≤ (m + 1 : ℕ) * p0) (Nat.cast_nonneg _)
    (layerKernelIndexBound_le_exp m hMP) hperiodExp hdegree hdim
    (by simpa only [Fintype.card_fin] using hcube) haxes
    (by simpa only [← Nat.card_eq_fintype_card] using hout)
    (fun j => by simpa only [← Nat.card_eq_fintype_card] using hrows j)
    hKcov hn hprofile
  have hlocal (r : positive) : mass r ≤ cap := by
    have hs := (allocatedRecenteredSpatialCoefficient_sum_le B U b S X modulus q wholeReference
      x N mesh hM selection hx hW hq hN hτ hbudget hperiod r.val).trans
      (div_le_div_of_nonneg_right hcost.2.2.2 hvolume.le)
    have hprod := finiteTripleCoefficientMass_le hs (hgridCost r) (hideal r)
    change mass r ≤ _ at hprod
    apply hprod.trans_eq
    dsimp only [cap, cost]
    rw [Real.exp_add, Real.exp_add]
    ring
  refine ⟨hlocal, ?_⟩
  have hcap : 0 ≤ cap := div_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) hvolume.le
  apply ((law).mean_mono (g := fun _ => cap) ?_).trans_eq ((law).mean_const cap)
  intro r
  split_ifs with hr
  · exact hlocal ⟨r, hr⟩
  · exact hcap

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq
variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (coverWitness : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S (residueRefinedPeriod modulus q) r.val)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (hR : ∀ j, 0 < R j)
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ : ℝ} (hW : 0 ≤ W)
variable (period : ℕ) [NeZero period]

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => {s : Finset (Fin dim) // s ∈ rowSets j})
local notation "tuples" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S)
local notation "refined" => residueRefinedPeriod modulus q
local notation "positive" => AllocatedPositiveResidue (dim := dim) B U b S refined
local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "law" => FiniteProbabilityWeights.fiberLaw
  (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)) (principalResidueLabel refined)

variable (F : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
  (allocatedPrincipalSides B U b S) → AllocatedFiniteIdealData (Fin dim) I n)

theorem allocatedConstructedSpatialCoefficient_coarse_bound
    {δ : ℝ≥0} {ε pI p0 pAccuracy w v E0 D O : ℝ}
    (hF : ∀ y₀ : tuples, (F y₀).Bounds B U b S rowSets x y₀ refined d period
      hb o bW hR δ ε pI (layerKernelIndexBound m M))
    {T C H : gridAxes → ℝ} {L : ℝ≥0}
    (hgrid : ∀ (r : positive) (a : gridAxes), ((coverWitness r).expansion a).Bounds (T a) (C a) (Real.exp O) L (H a))
    (hpI : 0 ≤ pI) (hp0 : 0 ≤ p0) (hpAccuracy : 0 ≤ pAccuracy)
    (hw : 0 ≤ w) (hv : 0 ≤ v) (hE0 : 0 ≤ E0) (hO : 0 ≤ O)
    (hgeom : AllocatedComparisonDimensions (G := G) B (Fin dim) rowTypes D)
    (hn : ∀ j, (n j : ℝ) ≤ D) (hKcov : ∀ j, (Fintype.card (Kcov j) : ℝ) ≤ D)
    (hdim : dim ≤ m + 1) (hG : (Fintype.card G : ℝ) ≤ p0) (hX : (Fintype.card X : ℝ) ≤ p0)
    (hMP : (M : ℝ) ≤ Real.exp p0) (hmod : modulus ≤ M ^ (m + 1))
    (hperiodM : period ≤ M ^ (m + 1))
    (hq : ∀ z, 0 < q z) (hN : ∀ z, 0 < N z) (hτ : 0 < τ)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection)) :
    let mesh : ℝ := allocatedProductCoarseMesh m X selection M modulus p0 pAccuracy w v E0
    let volume : ℝ := ∏ z, ∏ i, physicalSpatialOutputScale (Fin dim)
      (trimmedSpatialRootScale τ N q z) (trimmedSpatialSlopeScale W τ N q z) S.value i
    let cost : ℝ := coarseSpatialPartitionLog (allocatedProductCoarseInput m dim p0 pAccuracy w v E0) +
      allocatedFullGridCoefficientPreLog m D O +
      allocatedFiniteIdealMaskedLog m D pI ((m * 2 ^ (m + 1) : ℕ) * p0) ((m + 1 : ℕ) * p0)
    let cap : ℝ := ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖ * Real.exp cost / volume
    let mass := allocatedConstructedSpatialCoefficientAt (Kcov := Kcov)
      B U b S X modulus q wholeReference coverWitness d x hM selection hx hW period F mesh volume
    (∀ r, mass r ≤ cap) ∧
      (law).mean (fun r => if hr : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
          (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
          (Finset.univ.filter (fun y => principalResidueLabel refined y = r))
        then mass ⟨r, hr⟩ else 0) ≤ cap := by
  intro mesh volume cost cap mass
  rcases hgeom with ⟨hD, hdegree, _, hcube, haxes, _, _, hout, hrows, _, hprofile⟩
  have hscales (z : X) : 0 < trimmedSpatialRootScale τ N q z ∧
      0 < trimmedSpatialSlopeScale W τ N q z := trimmedSpatial_scales_pos hW hτ N q z (hN z) (hq z)
  have hvolume : 0 < volume := Finset.prod_pos (fun z _ => Finset.prod_pos (fun i _ =>
    physicalSpatialOutputScale_pos (Fin dim) (hscales z).1 (hscales z).2 (Nat.cast_pos.mpr S.positive) i))
  have hcost := allocatedProductCoarseMesh_partition_budget m X selection hp0 hpAccuracy hw hv hE0 hG hX hM hMP hmod
  have hgridCost := (allocatedFullGrid_coefficient_pre_bound B U b S refined coverWitness
    hgrid hO hdim haxes).1
  have hperiodExp : (period : ℝ) ≤ Real.exp ((m + 1 : ℕ) * p0) := by
    calc
      _ ≤ (M : ℝ) ^ (m + 1) := by exact_mod_cast hperiodM
      _ ≤ (Real.exp p0) ^ (m + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hMP _
      _ = _ := (Real.exp_nat_mul p0 (m + 1)).symm
  have hideal (r : positive) := allocatedFiniteIdeal_masked_coefficient_budget
    B U b S rowSets x ((coverWitness r).representative) refined d period hb o bW hR
    (F ((coverWitness r).representative)) (hF ((coverWitness r).representative))
    hpI hD (by positivity : 0 ≤ (m * 2 ^ (m + 1) : ℕ) * p0)
    (by positivity : 0 ≤ (m + 1 : ℕ) * p0) (Nat.cast_nonneg _)
    (layerKernelIndexBound_le_exp m hMP) hperiodExp hdegree hdim
    (by simpa only [Fintype.card_fin] using hcube) haxes
    (by simpa only [← Nat.card_eq_fintype_card] using hout)
    (fun j => by simpa only [← Nat.card_eq_fintype_card] using hrows j)
    hKcov hn hprofile
  have hlocal (r : positive) : mass r ≤ cap := by
    have hs := (allocatedRecenteredSpatialCoefficient_sum_le B U b S X modulus q wholeReference
      x N mesh hM selection hx hW hq hN hτ hbudget hperiod r.val).trans
      (div_le_div_of_nonneg_right hcost.2.2.2 hvolume.le)
    have hprod := finiteTripleCoefficientMass_le hs (hgridCost r) (hideal r)
    change mass r ≤ _ at hprod
    apply hprod.trans_eq
    dsimp only [cap, cost]
    rw [Real.exp_add, Real.exp_add]
    ring
  refine ⟨hlocal, ?_⟩
  have hcap : 0 ≤ cap := div_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) hvolume.le
  apply ((law).mean_mono (g := fun _ => cap) ?_).trans_eq ((law).mean_const cap)
  intro r
  split_ifs with hr
  · exact hlocal ⟨r, hr⟩
  · exact hcap

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

theorem finiteRepeatedCoefficientMass_le
    {T J K : Type*} [Fintype T] [Fintype J] [Fintype K]
    {L : T → Type*} [∀ t, Fintype (L t)] (c : T → J → K → ℂ) {A : ℝ}
    (hcard : ∀ t, (Fintype.card (L t) : ℝ) ≤ A) :
    (∑ t, ∑ j, ∑ k, ∑ _l : L t, ‖c t j k‖) ≤ A * ∑ t, ∑ j, ∑ k, ‖c t j k‖ := by
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_mul_of_nonneg_right (hcard t) (norm_nonneg _)

theorem finiteGridRepeatedCoefficientMass_le
    {A V W J K : Type*} [Fintype A] [Fintype V] [Fintype W] [Fintype J] [Fintype K]
    (e : A → ScalarSiteExpansion V)
    [gridPeriod : ∀ a (k : (e a).Term), NeZero ((e a).period k)]
    (c : (W × (∀ a, (e a).Term)) → J → K → ℂ)
    {T C H R : A → ℝ} {L : ℝ≥0}
    (he : ∀ a, (e a).Bounds (T a) (C a) (H a) L (R a))
    {D DS E : ℝ} (hD : 0 ≤ D) (hE : 0 ≤ E) (hA : (Fintype.card A : ℝ) ≤ D)
    (hS : (Fintype.card V : ℝ) ≤ DS) (hperiod : ∀ a, C a ≤ Real.exp E) :
    (∑ t, ∑ j, ∑ k, ∑ _l : V → ∀ a, ZMod ((e a).period (t.2 a)), ‖c t j k‖) ≤
      Real.exp (DS * D * E) * ∑ t, ∑ j, ∑ k, ‖c t j k‖ := by
  apply finiteRepeatedCoefficientMass_le
  intro t
  exact gridSiteResidueLabels_card_le_exp e t.2 he hD hE hA hS hperiod

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (coverWitness : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S (residueRefinedPeriod modulus q) r.val)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (hR : ∀ j, 0 < R j)
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ : ℝ} (hW : 0 ≤ W)
variable (period : ℕ) [NeZero period]

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => {s : Finset (Fin dim) // s ∈ rowSets j})
local notation "tuples" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S)
local notation "refined" => residueRefinedPeriod modulus q
local notation "positive" => AllocatedPositiveResidue (dim := dim) B U b S refined
local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "law" => FiniteProbabilityWeights.fiberLaw
  (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)) (principalResidueLabel refined)

variable (F : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
  (allocatedPrincipalSides B U b S) → AllocatedFiniteIdealData (Fin dim) I n)

variable [gridPeriodNeZero : ∀ (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q))
  (a : {a // allocatedGridAxis (I := I) U b S.value a}) (ki : ((coverWitness r).expansion a).Term),
  NeZero (((coverWitness r).expansion a).period ki)]

noncomputable def allocatedRefinedConstructedSpatialCoefficientAt (mesh volume : ℝ)
    (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) : ℝ :=
  let data : AllocatedFiniteIdealData (Fin dim) I n := F ((coverWitness r).representative)
  ∑ t : (X → SpatialSiteLabel (Fin dim) modulus 4 mesh) ×
      (∀ a, ((coverWitness r).expansion a).Term),
    ∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period)),
      ∑ i : data.Term,
        ∑ _gridLabel : Finset (Fin dim) → ∀ a, ZMod (((coverWitness r).expansion a).period (t.2 a)),
        ‖((allocatedSpatialExpansionCoefficient B U b S x X hM selection hx modulus hW mesh
            (principalResidueLabel modulus (wholeReference r.val)) t.1 / (volume : ℂ)) *
          coverSiteCoefficient (coverWitness r).expansion t.2) *
          allocatedProductMaskedIdealCoefficient B U b S rowSets x ((coverWitness r).representative)
            refined d period data.coefficient label i‖

omit [NeZero (residueRefinedPeriod modulus q)] in
theorem allocatedRefinedConstructedSpatialCoefficientAt_le (mesh volume : ℝ)
    {T C A H : gridAxes → ℝ} {L : ℝ≥0} {D Og : ℝ}
    (he : ∀ (r : positive) a, ((coverWitness r).expansion a).Bounds (T a) (C a) (A a) L (H a))
    (hD : 0 ≤ D) (hOg : 0 ≤ Og)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ D) (hdim : dim ≤ m + 1)
    (hperiodCap : ∀ a, C a ≤ Real.exp Og) (r : positive) :
    allocatedRefinedConstructedSpatialCoefficientAt (Kcov := Kcov)
      B U b S X modulus q wholeReference coverWitness d x hM selection hx hW period F mesh volume r ≤
      Real.exp ((2 ^ (m + 1) : ℕ) * D * Og) *
        allocatedConstructedSpatialCoefficientAt (Kcov := Kcov)
          B U b S X modulus q wholeReference coverWitness d x hM selection hx hW period F mesh volume r := by
  unfold allocatedRefinedConstructedSpatialCoefficientAt allocatedConstructedSpatialCoefficientAt
  dsimp only
  have hgrid : (Fintype.card gridAxes : ℝ) ≤ D :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans haxes
  have hsites : (Fintype.card (Finset (Fin dim)) : ℝ) ≤ (2 ^ (m + 1) : ℕ) := by
    simp only [Fintype.card_finset, Fintype.card_fin]
    exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ 2) hdim
  let data : AllocatedFiniteIdealData (Fin dim) I n := F ((coverWitness r).representative)
  let coefficient := fun (t : (X → SpatialSiteLabel (Fin dim) modulus 4 mesh) ×
      (∀ a, ((coverWitness r).expansion a).Term))
      (label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period)))
      (i : data.Term) =>
    ((allocatedSpatialExpansionCoefficient B U b S x X hM selection hx modulus hW mesh
      (principalResidueLabel modulus (wholeReference r.val)) t.1 / (volume : ℂ)) *
      coverSiteCoefficient (coverWitness r).expansion t.2) *
      allocatedProductMaskedIdealCoefficient B U b S rowSets x ((coverWitness r).representative)
        refined d period data.coefficient label i
  have hbound := finiteGridRepeatedCoefficientMass_le
    (A := gridAxes) (V := Finset (Fin dim))
    (W := X → SpatialSiteLabel (Fin dim) modulus 4 mesh)
    (J := Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period)))
    (K := data.Term) (coverWitness r).expansion
    (gridPeriod := fun a k => gridPeriodNeZero r a k)
    coefficient (he r) hD hOg hgrid hsites hperiodCap
  dsimp only [coefficient, data] at hbound
  convert hbound

theorem allocatedRefinedConstructedSpatialCoefficient_pre_bound
    {δ : ℝ≥0} {ε pI p0 E0 D O Og : ℝ}
    (hF : ∀ y₀ : tuples, (F y₀).Bounds B U b S rowSets x y₀ refined d period
      hb o bW hR δ ε pI (layerKernelIndexBound m M))
    {T C H : gridAxes → ℝ} {L : ℝ≥0}
    (hgrid : ∀ (r : positive) (a : gridAxes), ((coverWitness r).expansion a).Bounds (T a) (C a) (Real.exp O) L (H a))
    (hOg : 0 ≤ Og) (hperiodCap : ∀ a, C a ≤ Real.exp Og)
    (hpI : 0 ≤ pI) (hp0 : 0 ≤ p0) (hE0 : 0 ≤ E0) (hO : 0 ≤ O)
    (hgeom : AllocatedComparisonDimensions (G := G) B (Fin dim) rowTypes D)
    (hn : ∀ j, (n j : ℝ) ≤ D) (hKcov : ∀ j, (Fintype.card (Kcov j) : ℝ) ≤ D)
    (hdim : dim ≤ m + 1) (hG : (Fintype.card G : ℝ) ≤ p0) (hX : (Fintype.card X : ℝ) ≤ p0)
    (hMP : (M : ℝ) ≤ Real.exp p0) (hmod : modulus ≤ M ^ (m + 1))
    (hperiodM : period ≤ M ^ (m + 1))
    (hq : ∀ z, 0 < q z) (hN : ∀ z, 0 < N z) (hτ : 0 < τ)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection)) :
    let mesh : ℝ := allocatedEarlyRecenteredMesh X selection M modulus p0 E0
    let volume : ℝ := ∏ z, ∏ i, physicalSpatialOutputScale (Fin dim)
      (trimmedSpatialRootScale τ N q z) (trimmedSpatialSlopeScale W τ N q z) S.value i
    let cost : ℝ := coarseSpatialPartitionLog (allocatedEarlyCoarseInput m dim (p0 + E0)) +
      allocatedFullGridCoefficientPreLog m D O +
      allocatedFiniteIdealMaskedLog m D pI ((m * 2 ^ (m + 1) : ℕ) * p0) ((m + 1 : ℕ) * p0) +
      (2 ^ (m + 1) : ℕ) * D * Og
    let cap : ℝ := ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖ * Real.exp cost / volume
    let mass := allocatedRefinedConstructedSpatialCoefficientAt (Kcov := Kcov)
      B U b S X modulus q wholeReference coverWitness d x hM selection hx hW period F mesh volume
    (∀ r, mass r ≤ cap) ∧
      (law).mean (fun r => if hr : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
          (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
          (Finset.univ.filter (fun y => principalResidueLabel refined y = r))
        then mass ⟨r, hr⟩ else 0) ≤ cap := by
  intro mesh volume cost cap mass
  have hbase := allocatedConstructedSpatialCoefficient_pre_bound
    (B := B) (U := U) (b := b) (S := S) (X := X) (modulus := modulus) (q := q)
    (wholeReference := wholeReference) (coverWitness := coverWitness) (hb := hb) (o := o) (bW := bW)
    (d := d) (hR := hR) (x := x) (hM := hM) (selection := selection) (hx := hx)
    (N := N) (hW := hW) (period := period) (F := F)
    hF hgrid hpI hp0 hE0 hO hgeom hn hKcov hdim hG hX hMP hmod hperiodM hq hN hτ hbudget hperiod
  rcases hgeom with ⟨hD, _, _, _, haxes, _, _, _, _, _, _⟩
  have hrefine := allocatedRefinedConstructedSpatialCoefficientAt_le
    (B := B) (U := U) (b := b) (S := S) (X := X) (modulus := modulus) (q := q)
    (wholeReference := wholeReference) (coverWitness := coverWitness) (Kcov := Kcov)
    (d := d) (x := x) (hM := hM) (selection := selection) (hx := hx)
    (hW := hW) (period := period) (F := F) mesh volume hgrid hD hOg haxes hdim hperiodCap
  have hlocal (r : positive) : mass r ≤ cap := by
    apply (hrefine r).trans
    apply (mul_le_mul_of_nonneg_left (hbase.1 r) (Real.exp_pos _).le).trans_eq
    change Real.exp ((2 ^ (m + 1) : ℕ) * D * Og) *
      (‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖ *
        Real.exp (coarseSpatialPartitionLog (allocatedEarlyCoarseInput m dim (p0 + E0)) +
          allocatedFullGridCoefficientPreLog m D O +
          allocatedFiniteIdealMaskedLog m D pI ((m * 2 ^ (m + 1) : ℕ) * p0) ((m + 1 : ℕ) * p0)) / volume) = cap
    dsimp only [cap, cost]
    rw [Real.exp_add (coarseSpatialPartitionLog (allocatedEarlyCoarseInput m dim (p0 + E0)) +
      allocatedFullGridCoefficientPreLog m D O +
      allocatedFiniteIdealMaskedLog m D pI ((m * 2 ^ (m + 1) : ℕ) * p0) ((m + 1 : ℕ) * p0))
      ((2 ^ (m + 1) : ℕ) * D * Og)]
    ring
  have hscales (z : X) : 0 < trimmedSpatialRootScale τ N q z ∧
      0 < trimmedSpatialSlopeScale W τ N q z := trimmedSpatial_scales_pos hW hτ N q z (hN z) (hq z)
  have hvolume : 0 < volume := Finset.prod_pos (fun z _ => Finset.prod_pos (fun i _ =>
    physicalSpatialOutputScale_pos (Fin dim) (hscales z).1 (hscales z).2 (Nat.cast_pos.mpr S.positive) i))
  refine ⟨hlocal, ?_⟩
  have hcap : 0 ≤ cap := div_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) hvolume.le
  apply ((law).mean_mono (g := fun _ => cap) ?_).trans_eq ((law).mean_const cap)
  intro r
  split_ifs with hr
  · exact hlocal ⟨r, hr⟩
  · exact hcap

end Erdos3.VectorPolynomial

end

end OAI
