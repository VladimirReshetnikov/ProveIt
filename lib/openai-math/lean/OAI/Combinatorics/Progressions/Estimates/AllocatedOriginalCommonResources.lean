import OAI.Combinatorics.Progressions.Dynamics.AllocatedCoarseContinuousBudget
import OAI.Combinatorics.Progressions.Dynamics.PreparedModularGeneralNativeBudget
import OAI.Combinatorics.Progressions.Geometry.AllocatedOriginalCoarseBoxSource
import OAI.Combinatorics.Progressions.Probability.AllocatedRefinedCoefficientMass

namespace OAI

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

variable [gridPeriodNeZero : ∀ (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q))
  (a : {a // allocatedGridAxis (I := I) U b S.value a}) (ki : ((coverWitness r).expansion a).Term),
  NeZero (((coverWitness r).expansion a).period ki)]

theorem allocatedRefinedConstructedSpatialCoefficient_coarse_bound
    {δ : ℝ≥0} {ε pI p0 pAccuracy w v E0 D O Og : ℝ}
    (hF : ∀ y₀ : tuples, (F y₀).Bounds B U b S rowSets x y₀ refined d period
      hb o bW hR δ ε pI (layerKernelIndexBound m M))
    {T C H : gridAxes → ℝ} {L : ℝ≥0}
    (hgrid : ∀ (r : positive) (a : gridAxes), ((coverWitness r).expansion a).Bounds (T a) (C a) (Real.exp O) L (H a))
    (hOg : 0 ≤ Og) (hperiodCap : ∀ a, C a ≤ Real.exp Og)
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
  have hbase := allocatedConstructedSpatialCoefficient_coarse_bound
    (B := B) (U := U) (b := b) (S := S) (X := X) (modulus := modulus) (q := q)
    (wholeReference := wholeReference) (coverWitness := coverWitness) (hb := hb) (o := o) (bW := bW)
    (d := d) (hR := hR) (x := x) (hM := hM) (selection := selection) (hx := hx)
    (N := N) (hW := hW) (period := period) (F := F)
    hF hgrid hpI hp0 hpAccuracy hw hv hE0 hO hgeom hn hKcov hdim hG hX hMP hmod hperiodM hq hN hτ hbudget hperiod
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
        Real.exp (coarseSpatialPartitionLog (allocatedProductCoarseInput m dim p0 pAccuracy w v E0) +
          allocatedFullGridCoefficientPreLog m D O +
          allocatedFiniteIdealMaskedLog m D pI ((m * 2 ^ (m + 1) : ℕ) * p0) ((m + 1 : ℕ) * p0)) / volume) = cap
    dsimp only [cap, cost]
    rw [Real.exp_add (coarseSpatialPartitionLog (allocatedProductCoarseInput m dim p0 pAccuracy w v E0) +
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

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

theorem genuineCube_rescale_coefficient_bound
    {mass normalizer volume count C A B : ℝ}
    (hcount : 0 ≤ count) (hvolume : 0 < volume)
    (hraw : mass ≤ normalizer * Real.exp C / volume)
    (hinv : normalizer ≤ Real.exp A) (hratio : count / volume ≤ Real.exp B) :
    count * mass ≤ Real.exp (C + A + B) := by
  calc
    _ ≤ count * (normalizer * Real.exp C / volume) := mul_le_mul_of_nonneg_left hraw hcount
    _ = (normalizer * Real.exp C) * (count / volume) := by ring
    _ ≤ (Real.exp A * Real.exp C) * Real.exp B := mul_le_mul
      (mul_le_mul_of_nonneg_right hinv (Real.exp_pos _).le) hratio
      (div_nonneg hcount hvolume.le) (by positivity)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

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
variable (N : X → ℕ) {τ : ℝ}
local notation "W" => allocatedPhysicalRootBudget B U b S (fun _ => 0)
local notation "hW" => allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
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

theorem allocatedGenuineCubeCoefficient_pre_bound
    {δ : ℝ≥0} {ε pI p0 E0 D O Og pc gc V Q E : ℝ}
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
    (hpc : 0 ≤ pc) (hgc : 0 ≤ gc) (hV : 0 ≤ V) (hQ : 0 ≤ Q) (hE : 0 ≤ E)
    (hRadius : ∀ j, R j = allocatedCommonProductRadius m pc gc)
    (hCov : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp gc)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ V)
    (hqexp : ∀ z, (q z : ℝ) ≤ Real.exp Q) (hτexp : 1 / τ ≤ Real.exp E)
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
      (2 ^ (m + 1) : ℕ) * D * Og + allocatedCanonicalNormalizerLog m D pc gc +
      allocatedAmbientNormalizationLog dim p0 V Q E
    let mass := allocatedRefinedConstructedSpatialCoefficientAt (Kcov := Kcov)
      B U b S X modulus q wholeReference coverWitness d x hM selection hx hW period F mesh volume
    (∀ r, (integerBoxCubeCount N dim : ℝ) * mass r ≤ Real.exp cost) ∧
      (law).mean (fun r => if hr : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
          (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
          (Finset.univ.filter (fun y => principalResidueLabel refined y = r))
        then (integerBoxCubeCount N dim : ℝ) * mass ⟨r, hr⟩ else 0) ≤ Real.exp cost := by
  intro mesh volume cost mass
  have hbase := allocatedRefinedConstructedSpatialCoefficient_pre_bound
    (B := B) (U := U) (b := b) (S := S) (X := X) (modulus := modulus) (q := q)
    (wholeReference := wholeReference) (coverWitness := coverWitness) (hb := hb) (o := o) (bW := bW)
    (d := d) (hR := hR) (x := x) (hM := hM) (selection := selection) (hx := hx)
    (N := N) (τ := τ) (period := period) (F := F)
    hW hF hgrid hOg hperiodCap hpI hp0 hE0 hO hgeom hn hKcov hdim hG hX hMP hmod hperiodM
    hq hN hτ (le_refl _) hperiod
  have hinv := allocatedCanonicalIdealNormalizer_pre_bound B U b S hpc hgc hgeom hRadius hCov
  have hratio := (allocatedAmbientVolume_pre_bound (dim := dim) (τ := τ) B U b S N q
    hV hQ hE hvars hX hN hq hτ hqexp hτexp).2
  have hscales (z : X) : 0 < trimmedSpatialRootScale τ N q z ∧
      0 < trimmedSpatialSlopeScale W τ N q z := trimmedSpatial_scales_pos hW hτ N q z (hN z) (hq z)
  have hvolume : 0 < volume := Finset.prod_pos (fun z _ => Finset.prod_pos (fun i _ =>
    physicalSpatialOutputScale_pos (Fin dim) (hscales z).1 (hscales z).2 (Nat.cast_pos.mpr S.positive) i))
  have hlocal (r : positive) : (integerBoxCubeCount N dim : ℝ) * mass r ≤ Real.exp cost := by
    exact genuineCube_rescale_coefficient_bound (Nat.cast_nonneg _) hvolume (hbase.1 r) hinv hratio
  refine ⟨hlocal, ?_⟩
  apply ((law).mean_mono (g := fun _ => Real.exp cost) ?_).trans_eq ((law).mean_const (Real.exp cost))
  intro r
  split_ifs with hr
  · exact hlocal ⟨r, hr⟩
  · exact (Real.exp_pos _).le

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

theorem genuineCube_rescale_joint_coefficient_bound
    {mass normalizer volume count C A B Z : ℝ}
    (hcount : 0 ≤ count) (hvolume : 0 < volume)
    (hraw : mass ≤ normalizer * Real.exp C / volume)
    (hinv : normalizer ≤ Real.exp A) (hratio : count / volume ≤ Real.exp B)
    (hZ : 0 < Z) (hZi : Z⁻¹ ≤ 2) :
    count * mass / Z ≤ Real.exp (C + A + B + 1) := by
  have hraw' := genuineCube_rescale_coefficient_bound hcount hvolume hraw hinv hratio
  calc
    _ = (count * mass) * Z⁻¹ := div_eq_mul_inv _ _
    _ ≤ Real.exp (C + A + B) * 2 :=
      mul_le_mul hraw' hZi (inv_nonneg.mpr hZ.le) (Real.exp_pos _).le
    _ ≤ Real.exp (C + A + B) * Real.exp 1 :=
      mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

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
variable (N : X → ℕ) {τ : ℝ}
local notation "W" => allocatedPhysicalRootBudget B U b S (fun _ => 0)
local notation "hW" => allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
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

theorem allocatedGenuineCubeCoefficient_coarse_bound
    {δ : ℝ≥0} {ε pI p0 pAccuracy w v E0 D O Og pc gc V Q E Z : ℝ}
    (hF : ∀ y₀ : tuples, (F y₀).Bounds B U b S rowSets x y₀ refined d period
      hb o bW hR δ ε pI (layerKernelIndexBound m M))
    {T C H : gridAxes → ℝ} {L : ℝ≥0}
    (hgrid : ∀ (r : positive) (a : gridAxes), ((coverWitness r).expansion a).Bounds (T a) (C a) (Real.exp O) L (H a))
    (hOg : 0 ≤ Og) (hperiodCap : ∀ a, C a ≤ Real.exp Og)
    (hpI : 0 ≤ pI) (hp0 : 0 ≤ p0) (hpAccuracy : 0 ≤ pAccuracy)
    (hw : 0 ≤ w) (hv : 0 ≤ v) (hE0 : 0 ≤ E0) (hO : 0 ≤ O)
    (hgeom : AllocatedComparisonDimensions (G := G) B (Fin dim) rowTypes D)
    (hn : ∀ j, (n j : ℝ) ≤ D) (hKcov : ∀ j, (Fintype.card (Kcov j) : ℝ) ≤ D)
    (hdim : dim ≤ m + 1) (hG : (Fintype.card G : ℝ) ≤ p0) (hX : (Fintype.card X : ℝ) ≤ p0)
    (hMP : (M : ℝ) ≤ Real.exp p0) (hmod : modulus ≤ M ^ (m + 1))
    (hperiodM : period ≤ M ^ (m + 1))
    (hq : ∀ z, 0 < q z) (hN : ∀ z, 0 < N z) (hτ : 0 < τ)
    (hpc : 0 ≤ pc) (hgc : 0 ≤ gc) (hV : 0 ≤ V) (hQ : 0 ≤ Q) (hE : 0 ≤ E)
    (hZ : 0 < Z) (hZi : Z⁻¹ ≤ 2)
    (hRadius : ∀ j, R j = allocatedCommonProductRadius m pc gc)
    (hCov : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp gc)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ V)
    (hqexp : ∀ z, (q z : ℝ) ≤ Real.exp Q) (hτexp : 1 / τ ≤ Real.exp E)
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
      allocatedFiniteIdealMaskedLog m D pI ((m * 2 ^ (m + 1) : ℕ) * p0) ((m + 1 : ℕ) * p0) +
      (2 ^ (m + 1) : ℕ) * D * Og + allocatedCanonicalNormalizerLog m D pc gc +
      allocatedAmbientNormalizationLog dim p0 V Q E + 1
    let mass := allocatedRefinedConstructedSpatialCoefficientAt (Kcov := Kcov)
      B U b S X modulus q wholeReference coverWitness d x hM selection hx hW period F mesh volume
    (∀ r, (integerBoxCubeCount N dim : ℝ) * mass r / Z ≤ Real.exp cost) ∧
      (law).mean (fun r => if hr : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
          (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
          (Finset.univ.filter (fun y => principalResidueLabel refined y = r))
        then (integerBoxCubeCount N dim : ℝ) * mass ⟨r, hr⟩ / Z else 0) ≤ Real.exp cost := by
  intro mesh volume cost mass
  have hbase := allocatedRefinedConstructedSpatialCoefficient_coarse_bound
    (B := B) (U := U) (b := b) (S := S) (X := X) (modulus := modulus) (q := q)
    (wholeReference := wholeReference) (coverWitness := coverWitness) (hb := hb) (o := o) (bW := bW)
    (d := d) (hR := hR) (x := x) (hM := hM) (selection := selection) (hx := hx)
    (N := N) (τ := τ) (period := period) (F := F)
    hW hF hgrid hOg hperiodCap hpI hp0 hpAccuracy hw hv hE0 hO hgeom hn hKcov hdim hG hX hMP hmod hperiodM
    hq hN hτ (le_refl _) hperiod
  have hinv := allocatedCanonicalIdealNormalizer_pre_bound B U b S hpc hgc hgeom hRadius hCov
  have hratio := (allocatedAmbientVolume_pre_bound (dim := dim) (τ := τ) B U b S N q
    hV hQ hE hvars hX hN hq hτ hqexp hτexp).2
  have hscales (z : X) : 0 < trimmedSpatialRootScale τ N q z ∧
      0 < trimmedSpatialSlopeScale W τ N q z := trimmedSpatial_scales_pos hW hτ N q z (hN z) (hq z)
  have hvolume : 0 < volume := Finset.prod_pos (fun z _ => Finset.prod_pos (fun i _ =>
    physicalSpatialOutputScale_pos (Fin dim) (hscales z).1 (hscales z).2 (Nat.cast_pos.mpr S.positive) i))
  have hlocal (r : positive) : (integerBoxCubeCount N dim : ℝ) * mass r / Z ≤ Real.exp cost := by
    exact genuineCube_rescale_joint_coefficient_bound (Nat.cast_nonneg _) hvolume
      (hbase.1 r) hinv hratio hZ hZi
  refine ⟨hlocal, ?_⟩
  apply ((law).mean_mono (g := fun _ => Real.exp cost) ?_).trans_eq ((law).mean_const (Real.exp cost))
  intro r
  split_ifs with hr
  · exact hlocal ⟨r, hr⟩
  · exact (Real.exp_pos _).le

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq fullBooleanRowSetFintype

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
variable (N : X → ℕ) {τ : ℝ}
local notation "W" => allocatedPhysicalRootBudget B U b S (fun _ => 0)
local notation "hW" => allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
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

variable (base : X → ℤ)

def AllocatedCoarseFamilyResources
    (pI p0 pAccuracy w v E0 D O pc gc Pτ Z : ℝ) : Prop :=
  let meshR := allocatedProductCoarseMesh m X selection M modulus p0 pAccuracy w v E0
  let mesh : ℝ≥0 := ⟨meshR,
    (allocatedProductCoarseMesh_pos m X selection M modulus p0 pAccuracy w v E0).le⟩
  let volume : ℝ := ∏ z, ∏ i, physicalSpatialOutputScale (Fin dim)
    (trimmedSpatialRootScale τ N q z) (trimmedSpatialSlopeScale W τ N q z) S.value i
  let cost : ℝ := coarseSpatialPartitionLog (allocatedProductCoarseInput m dim p0 pAccuracy w v E0) +
    allocatedFullGridCoefficientPreLog m D O +
    allocatedFiniteIdealMaskedLog m D pI ((m * 2 ^ (m + 1) : ℕ) * p0) ((m + 1 : ℕ) * p0) +
    (2 ^ (m + 1) : ℕ) * D * O + allocatedCanonicalNormalizerLog m D pc gc +
    allocatedAmbientNormalizationLog dim p0 D p0 Pτ + 1
  let mass := allocatedRefinedConstructedSpatialCoefficientAt (Kcov := Kcov)
    B U b S X modulus q wholeReference coverWitness d x hM selection hx hW period F meshR volume
  (∀ r, (integerBoxCubeCount N dim : ℝ) * mass r / Z ≤ Real.exp cost) ∧
  (law).mean (fun r => if hr : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
      (Finset.univ.filter (fun y => principalResidueLabel refined y = r))
    then (integerBoxCubeCount N dim : ℝ) * mass ⟨r, hr⟩ / Z else 0) ≤ Real.exp cost ∧
  ∀ (r : positive)
    (a : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q)
    (spatial : X → SpatialSiteLabel (Fin dim) modulus 4 mesh)
    (kg : ∀ i, ((coverWitness r).expansion i).Term)
    (i : (F (coverWitness r).representative).Term) (s : Finset (Fin dim))
    (gridLabel : ∀ j, ZMod (((coverWitness r).expansion j).period (kg j))),
    (∀ z, ‖allocatedRecenteredContinuousSiteFactor (τ := τ) B U b S X modulus q wholeReference
      coverWitness x N mesh base r a spatial kg ((F (coverWitness r).representative).factor i s) s gridLabel z‖ ≤ 1) ∧
    LipschitzWith
      ⟨Real.exp (allocatedCoarseContinuousLog m dim D pI p0 pAccuracy w v E0 O Pτ
        (normalizedSiteCutoffBound : ℝ)), Real.exp_nonneg _⟩
      (allocatedRecenteredContinuousSiteFactor (τ := τ) B U b S X modulus q wholeReference
        coverWitness x N mesh base r a spatial kg ((F (coverWitness r).representative).factor i s) s gridLabel)

theorem allocatedCoarseFamilyResources_of_bounds
    {δ : ℝ≥0} {ε pI p0 pAccuracy w v E0 D O pc gc Pτ Z : ℝ}
    (hF : ∀ y₀ : tuples, (F y₀).Bounds B U b S rowSets x y₀ refined d period
      hb o bW hR δ ε pI (layerKernelIndexBound m M))
    {T H : gridAxes → ℝ}
    (hgrid : ∀ (r : positive) (a : gridAxes), ((coverWitness r).expansion a).Bounds
      (T a) (Real.exp O) (Real.exp O) ⟨Real.exp O, Real.exp_nonneg _⟩ (H a))
    (hpI : 0 ≤ pI) (hp0 : 0 ≤ p0) (hpAccuracy : 0 ≤ pAccuracy)
    (hw : 0 ≤ w) (hv : 0 ≤ v) (hE0 : 0 ≤ E0) (hO : 0 ≤ O)
    (hpc : 0 ≤ pc) (hgc : 0 ≤ gc) (hPτ : 0 ≤ Pτ)
    (hgeom : AllocatedComparisonDimensions (G := G) B (Fin dim) rowTypes D)
    (hn : ∀ j, (n j : ℝ) ≤ D) (hKcov : ∀ j, (Fintype.card (Kcov j) : ℝ) ≤ D)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ D)
    (hdim : dim ≤ m + 1) (hG : (Fintype.card G : ℝ) ≤ p0) (hX : (Fintype.card X : ℝ) ≤ p0)
    (hMP : (M : ℝ) ≤ Real.exp p0) (hmod : modulus ≤ M ^ (m + 1))
    (hperiodM : period ≤ M ^ (m + 1))
    (hq : ∀ z, 0 < q z) (hN : ∀ z, 0 < N z) (hτ : 0 < τ)
    (hRadius : ∀ j, R j = allocatedCommonProductRadius m pc gc)
    (hCov : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp gc)
    (hqexp : ∀ z, (q z : ℝ) ≤ Real.exp p0) (hτexp : 1 / τ ≤ Real.exp Pτ)
    (hZ : 0 < Z) (hZi : Z⁻¹ ≤ 2)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection)) :
    AllocatedCoarseFamilyResources (Kcov := Kcov) (τ := τ)
      B U b S X modulus q wholeReference coverWitness d x hM selection hx N period F base
      pI p0 pAccuracy w v E0 D O pc gc Pτ Z := by
  unfold AllocatedCoarseFamilyResources
  intro meshR mesh volume cost mass
  have hD : 0 ≤ D := by
    obtain ⟨hD, _⟩ := hgeom
    exact hD
  have hcoeff := allocatedGenuineCubeCoefficient_coarse_bound
    (B := B) (U := U) (b := b) (S := S) (X := X) (modulus := modulus) (q := q)
    (wholeReference := wholeReference) (coverWitness := coverWitness) (hb := hb) (o := o) (bW := bW)
    (d := d) (hR := hR) (x := x) (hM := hM) (selection := selection) (hx := hx)
    (N := N) (τ := τ) (period := period) (F := F)
    hF hgrid hO (fun _ => le_rfl) hpI hp0 hpAccuracy hw hv hE0 hO hgeom hn hKcov hdim hG hX
    hMP hmod hperiodM hq hN hτ hpc hgc hD hp0 hPτ hZ hZi hRadius hCov hvars hqexp hτexp hperiod
  refine ⟨hcoeff.1, hcoeff.2, ?_⟩
  intro r a
  exact allocatedCoarseContinuousSiteFactor_bounds
    (B := B) (U := U) (b := b) (S := S) (X := X) (modulus := modulus) (q := q)
    (wholeReference := wholeReference) (coverWitness := coverWitness) (x := x) (N := N)
    (τ := τ) (base := base) (r := r) (a := a) (hb := hb) (o := o) (bW := bW)
    (d := d) (period := period) (hR := hR) (selection := selection)
    (F := F (coverWitness r).representative)
    (hF _) (hgrid r) hpI hp0 hpAccuracy hw hv hE0 hO hPτ hgeom hG hX hM hMP hmod hq hN hτ hτexp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq fullGridCoverAxisDecidableEq

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) (Fin.val j + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : jets j → Finset (Fin dim)))
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "fullRows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

def AllocatedOriginalGenuineResourcesData (Psp E e pNum Pbase Qraw pAccuracy pSampling Dgeom cgeom O pc gc Pτ : ℝ) (hP : 0 ≤ Psp)
    (δ : ℝ≥0) (A Kraw Ksite Kgen : ℕ)
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val)
    (M Dwin : ℕ) (hM : 0 < M) (hDwin : 0 < Dwin) (η : ℝ) (hη : 0 < η) : Prop :=
  ∃ hgridPeriod : ∀ (q : AllocatedRefinedPeriodIndex m Psp)
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ))
      (a : {a // allocatedGridAxis (I := I) U b S.value a})
      (k : ((witnesses q r).expansion a).Term),
      0 < ((witnesses q r).expansion a).period k,
  let w := allocatedSiteKernelMaskLog m Psp
  let v := allocatedIdealProfileLog m pAccuracy e
  let Pfinal := sourceCoverParameter dim Kraw Psp pNum Qraw
    (allocatedSiteErrorFourierOutput m pSampling w v)
    (allocatedSeparatedGeometryLog m Psp pAccuracy pSampling w v (E + 2))
  let Mk := scalarKernelCutoff (Fin dim) G M Dwin η
  let hMk := (scalarKernelCutoff_bounds (Fin dim) G hM hDwin hη).1
  ∀ (selection : Fin dim ↪ G) (_hqDim : dim ≤ m + 1)
    (_hcard : dim * (dim + 2) ≤ Fintype.card G) [Nonempty (Fin dim)]
    (hMkPsp : (Mk : ℝ) ≤ Real.exp Psp) (hlarge : Mk ≤ S.value)
    (_hG : (Fintype.card G : ℝ) ≤ Psp) (_hdimP : ((dim + 1 : ℕ) : ℝ) ≤ Psp)
    (_hDexp : Dgeom ≤ Real.exp Psp) (_hpAccuracy : 0 ≤ pAccuracy) (_he : 0 ≤ e)
    (_hE : 0 ≤ E) (_hcgeom : 0 ≤ cgeom) (_hO : 0 ≤ O)
    (_hpc : 0 ≤ pc) (_hgc : 0 ≤ gc) (_hPτ : 0 ≤ Pτ)
    (_hδ : 0 < δ) (_hδ1 : δ ≤ 1) (_hδe : (δ : ℝ)⁻¹ ≤ Real.exp e)
    (_hKgen : 2 ≤ Kgen)
    (_hSampling : PhysicalAmbientRowsKernelSampling.{uX,uJ,0} m dim Kgen
      (fun j => (rowSets j : Type)) fullRows),
  let Kernel := G → IntegerScalarCubeBox (Fin dim) S.value
  let Good := GoodScalarKernelTuple (L := S.value) selection (1 / (Mk : ℝ)) Mk
  let GoodKernel := {x : Kernel // Good x}
  ∃ (d : GoodKernel → ℕ) (hd : ∀ x, 0 < d x),
    let : ∀ x, NeZero (d x) := fun x => ⟨(hd x).ne'⟩
    (∀ x, (d x : ℝ) ≤ Real.exp ((Pbase + A) ^ A)) ∧
  ∃ (modulus : GoodKernel → ℕ) (hmodulus : ∀ x, 0 < modulus x),
    let : ∀ x, NeZero (modulus x) := fun x => ⟨(hmodulus x).ne'⟩
    ∃ hmodulusSize : ∀ x, modulus x ≤ Mk ^ (m + 1),
    (∀ (x : GoodKernel) (root : G → ℤ), integerScalarLattice (Unit ⊕ Fin dim) (modulus x : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x.val) selection)
        (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x.val) selection)) ∧
    (∀ (x : GoodKernel) j, integerScalarLattice (jets j) (modulus x : ℤ) ≤
      (scalarKernelIntegerJet x.val (j.val + 1) (jetRows j)).mulVecLin.range) ∧
    ∀ (_block : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, jets a.val.1 ↪ B a.val)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin dim)) U)] [BorelSpace (SiteTorus (Finset (Fin dim)) U)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Kcov : Fin m → Type uQ} [∀ j, Fintype (Kcov j)]
    (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hCp : ∀ j, (C j : ℝ) ≤ Real.exp pNum) (_hVp : ∀ j, (V j : ℝ) ≤ Real.exp pNum)
    (_hCpAccuracy : ∀ j, (C j : ℝ) ≤ Real.exp pAccuracy)
    (_hVpAccuracy : ∀ j, (V j : ℝ) ≤ Real.exp pAccuracy)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hgeom : AllocatedComparisonDimensions (G := G) B (Fin dim) (fun j => (rowSets j : Type)) Dgeom)
    (_hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Dgeom)
    (_hIgeom : ∀ j, (Fintype.card (I j) : ℝ) ≤ Dgeom)
    (_hngeom : ∀ j, (n j : ℝ) ≤ Dgeom)
    (_hKcov : ∀ j, (Fintype.card (Kcov j) : ℝ) ≤ Dgeom)
    (_hCgeom : ∀ j, Cinv j ≤ Real.exp cgeom)
    (_hsmall : ∀ j, R j ≤ allocatedProductChartRadius m Dgeom cgeom)
    (_hRadius : ∀ j, R j = allocatedCommonProductRadius m pc gc)
    (_hCovEarly : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp gc)
    (_hσ1 : ∀ j, σ j ≤ 1)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μsmall : Measure (CoefficientTorus (K := Fin dim) U)) [μsmall.IsAddLeftInvariant] [IsProbabilityMeasure μsmall]
    {X : Type uX} [Fintype X] [DecidableEq X]
    (hXPsp : (Fintype.card X : ℝ) ≤ Psp)
    (q : X → ℕ) (hq : ∀ t, 0 < q t) (hqPsp : ∀ t, (q t : ℝ) ≤ Real.exp Psp),
    let refined := fun x => residueRefinedPeriod (modulus x) q
    let index := fun x => allocatedRefinedPeriodIndex m hP hMkPsp
      (hmodulusSize x)
      hXPsp (hmodulus x) q hq hqPsp
    let : ∀ x, NeZero (refined x) := fun x => ⟨(residueRefinedPeriod_pos (hmodulus x) q hq).ne'⟩
    let W := allocatedPhysicalRootBudget B U b S (fun _ => 0)
    let hW := allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)
    let indices := PrincipalTupleIndex B (layerSamplerDegree I n)
    let ξ := normalizedTupleNarrowWidth X indices selection Mk Psp ((E + 2) + 2)
    let hξ := normalizedTupleNarrowWidth_pos X indices selection Mk Psp ((E + 2) + 2)
    let mesh := fun x : GoodKernel =>
      allocatedProductCoarseMesh m X selection Mk (modulus x) Psp pAccuracy w v (E + 2)
    ∀ {τ : ℝ} (hτ : 0 < τ) (_hτP : 1 / τ ≤ Real.exp pNum)
    (_hτEarly : 1 / τ ≤ Real.exp Pτ) (_hτ1 : τ ≤ 1 / 2)
    {Psrc Psamp : ℝ} (_hnum : AllocatedSourceNumerics B U b S C V Psrc)
    (_hPsamp : Psp ≤ Psamp) (_hdimPsamp : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ Psamp)
    (_hτPsamp : 1 / τ ≤ Real.exp Psamp)
    (N : X → ℕ) (hN : ∀ t, 0 < N t)
    (_hsize : ∀ t, Real.exp ((Pfinal + Ksite) ^ Ksite) ≤ (N t : ℝ))
    (_hsizeBox : ∀ t, 4 ≤ τ * (N t : ℝ))
    (_hsizeG : ∀ t, Real.exp ((allocatedCutoffSamplingLog m dim Psrc
      (normalizedSiteCutoffBound : ℝ) 0 Psamp + Kgen) ^ Kgen) ≤ (N t : ℝ))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
    {rank : ℝ}
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) rank (U j) (poly j))
    (_hRank : Real.exp ((Pfinal + Ksite) ^ Ksite) ≤ rank)
    (_hRankG : Real.exp ((allocatedCutoffSamplingLog m dim Psrc
      (normalizedSiteCutoffBound : ℝ) 0 Psamp + Kgen) ^ Kgen) ≤ rank)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (_hcells : cells.Nonempty)
    (bases : Finset (X → ℤ)) (_hbases : bases.Nonempty)
    (_hbaseBox : ∀ base ∈ bases, base ∈ trimmedIntegerBox N (spatialTrimMargin τ N)),
    let V₀ := narrowTrimmedSpatialWidths (G := G) (J := indices) W τ ξ N
    let Z := selectedJointDensityMass bases q cells V₀
      (allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem)
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let wholeReference := fun x => allocatedSupportedWholeReference (dim := dim) B U b S (refined x)
    let idealLog := allocatedGenuineComparisonErrorLog m Psp Dgeom cgeom
      (coarseSpatialPartitionLog (allocatedProductCoarseInput m dim Psp pAccuracy w v (E + 2))) O E
    ∃ hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells V₀ z,
    (|Z - 1| ≤ Real.exp (-Qraw) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2) ∧
    ∃ t : GoodKernel → (X → ℤ) → Fin Mk,
      (∀ x base, kernelPeriodCandidate (m + 1) (t x base) ≤ Mk ^ (m + 1)) ∧
    ∃ F : GoodKernel → (X → ℤ) →
        PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S) →
        AllocatedFiniteIdealData (Fin dim) I n,
      (∀ x base y₀, (F x base y₀).Bounds B U b S rowSets x.val y₀ (refined x) (d x)
        (kernelPeriodCandidate (m + 1) (t x base)) hb o bW hR δ (Real.exp (-idealLog))
        (allocatedFiniteIdealInputLog m Dgeom e idealLog) (layerKernelIndexBound m Mk)) ∧
      (∀ x base,
        let _ : ∀ (r : AllocatedPositiveResidue (dim := dim) B U b S (refined x))
            (a : {a // allocatedGridAxis (I := I) U b S.value a})
            (k : ((witnesses (index x) r).expansion a).Term),
            NeZero (((witnesses (index x) r).expansion a).period k) :=
          fun r a k => ⟨(hgridPeriod (index x) r a k).ne'⟩
        AllocatedCoarseFamilyResources (Kcov := Kcov) (τ := τ)
          B U b S X (modulus x) q (wholeReference x) (witnesses (index x))
          (d x) x.val hMk selection x.property N (kernelPeriodCandidate (m + 1) (t x base))
          (F x base) base (allocatedFiniteIdealInputLog m Dgeom e idealLog)
          Psp pAccuracy w v (E + 2) Dgeom O pc gc Pτ Z) ∧
    ∀ (test : Finset (Fin dim) → (X → ℝ) → ℂ), (∀ site z, ‖test site z‖ ≤ 1) →
    let genuine := fun (x : GoodKernel) base =>
      (law.fiberLaw (principalResidueLabel (refined x))).complexMean (fun r =>
        if hr : 0 < law.mass (Finset.univ.filter (fun y => principalResidueLabel (refined x) y = r)) then
          let rr : AllocatedPositiveResidue (dim := dim) B U b S (refined x) := ⟨r, hr⟩
          let _ : ∀ (a : {a // allocatedGridAxis (I := I) U b S.value a})
              (k : ((witnesses (index x) rr).expansion a).Term),
              NeZero (((witnesses (index x) rr).expansion a).period k) :=
            fun a k => ⟨(hgridPeriod (index x) rr a k).ne'⟩
          ∑ a : cells, (selectedResidueCellWeight q cells V₀ a : ℂ) *
            ((integerBoxCubeCount N dim : ℂ) *
              𝔼 cube : SupportedCube dim (integerBox N : Set (X → ℤ)),
                allocatedAmbientNormalizedSpatialApproximation (τ := τ) B U b S X (modulus x) q
                  (wholeReference x) (witnesses (index x)) hb o bW (d x) x.val hMk selection x.property N hW
                  ⟨mesh x, (allocatedProductCoarseMesh_pos m X selection Mk (modulus x)
                    Psp pAccuracy w v (E + 2)).le⟩ base cells poly hmem rr a
                  (kernelPeriodCandidate (m + 1) (t x base))
                  (F x base ((witnesses (index x) rr).representative)).coefficient
                  (F x base ((witnesses (index x) rr).representative)).factor test
                  ((physicalCubeParametersEquiv X dim).symm cube.val))
        else 0) / (Z : ℂ)
    ∀ (window : G → ℕ) (hwindow : ∀ g, window g ≤ S.value)
      (hDwindow : ∀ g, S.value ≤ Dwin * window g)
      (shift : G → ℤ) (moduli : G → Option (Fin dim) → ℕ)
      (residues : ∀ g i, ZMod (moduli g i))
      (hmoduli : ∀ g i, 0 < moduli g i) (hmoduliM : ∀ g i, moduli g i ≤ M),
    let kernelLaw := FiniteProbabilityWeights.pi (fun g =>
      affineScalarCubeWindowWeights (Fin dim) S.value (window g) M Dwin (shift g) S.positive
        (hwindow g) (hDwindow g) (moduli g) (residues g) (hmoduli g) (hmoduliM g)
        (scalarKernelCutoff_window_size (Fin dim) G hM hDwin hη hlarge (hDwindow g)))
    ‖kernelLaw.complexMean (fun x => 𝔼 base ∈ bases,
        allocatedOriginalTupleSource B U b hR hσ S x X q hb o N hN hW hτ hξ base cells hmass
          (physicalCubeSiteTest test) Z poly hmem) -
      kernelLaw.goodPartBaseMean bases Good (fun x hx base => genuine ⟨x, hx⟩ base)‖ ≤ 2 * Real.exp (-E) + η

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem allocatedCanonicalTrim_bounds {P : ℝ} (hP : 1 ≤ P) :
    0 < Real.exp (-P) ∧ Real.exp (-P) ≤ 1 / 2 ∧ 1 / Real.exp (-P) = Real.exp P := by
  have htwo : (2 : ℝ) ≤ Real.exp P := by linarith [Real.add_one_le_exp P]
  refine ⟨Real.exp_pos _, ?_, ?_⟩
  · simpa only [Real.exp_neg, one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) htwo)
  · rw [Real.exp_neg, one_div, inv_inv]

theorem allocatedCanonicalSampling_bounds (dim : ℕ) (X : Type*) [Fintype X]
    {P : ℝ} (hP : 0 ≤ P) (hX : (Fintype.card X : ℝ) ≤ P) :
    let Psamp : ℝ := (dim + 2 : ℕ) * P
    P ≤ Psamp ∧ (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ Psamp ∧
      1 / Real.exp (-P) ≤ Real.exp Psamp := by
  intro Psamp
  have hd : (0 : ℝ) ≤ dim := Nat.cast_nonneg _
  have hPP : P ≤ Psamp := by dsimp [Psamp]; push_cast; nlinarith
  refine ⟨hPP, ?_, ?_⟩
  · simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_fin, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    dsimp [Psamp]
    push_cast
    nlinarith
  · rw [Real.exp_neg, one_div, inv_inv]
    exact Real.exp_le_exp.mpr hPP

def allocatedCanonicalCubeThreshold (P original genuine : ℝ) : ℝ :=
  max original (max genuine (P + 4))

theorem allocatedCanonicalCubeThreshold_bounds (P original genuine : ℝ) {N : ℝ}
    (hN : Real.exp (allocatedCanonicalCubeThreshold P original genuine) ≤ N) :
    Real.exp original ≤ N ∧ Real.exp genuine ≤ N ∧ 4 ≤ Real.exp (-P) * N := by
  have ho : original ≤ allocatedCanonicalCubeThreshold P original genuine := le_max_left _ _
  have hg : genuine ≤ allocatedCanonicalCubeThreshold P original genuine :=
    (le_max_left _ _).trans (le_max_right _ _)
  have htrim : P + 4 ≤ allocatedCanonicalCubeThreshold P original genuine :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨(Real.exp_le_exp.mpr ho).trans hN, (Real.exp_le_exp.mpr hg).trans hN, ?_⟩
  calc
    (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
    _ = Real.exp (-P) * Real.exp (P + 4) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-P) * N := mul_le_mul_of_nonneg_left
      ((Real.exp_le_exp.mpr htrim).trans hN) (Real.exp_pos _).le

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq fullGridCoverAxisDecidableEq

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) (Fin.val j + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : jets j → Finset (Fin dim)))
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "fullRows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

theorem allocatedOriginalGenuineResourcesData_of_coarse
    {Psp E e pNum Pbase Qraw pAccuracy pSampling Dgeom cgeom O pc gc Pτ : ℝ} (hP : 0 ≤ Psp)
    {δ : ℝ≥0} {A Kraw Ksite Kgen : ℕ}
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val)
    {Nt Hs : (q : AllocatedRefinedPeriodIndex m Psp) →
      {a // allocatedGridAxis (I := I) U b S.value a} → ℝ}
    (hgrid : ∀ q r a, ((witnesses q r).expansion a).Bounds
      (Nt q a) (Real.exp O) (Real.exp O) ⟨Real.exp O, Real.exp_nonneg _⟩ (Hs q a))
    (M Dwin : ℕ) (hM : 0 < M) (hDwin : 0 < Dwin) (η : ℝ) (hη : 0 < η)
    (hcoarse : AllocatedProductCoarseBoxAffineData.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp E e pNum Pbase Qraw pAccuracy pSampling hP δ A Kraw Ksite witnesses
      M Dwin hM hDwin η hη) :
    AllocatedOriginalGenuineResourcesData.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp E e pNum Pbase Qraw pAccuracy pSampling Dgeom cgeom O pc gc Pτ hP δ
      A Kraw Ksite Kgen witnesses M Dwin hM hDwin η hη := by
  unfold AllocatedOriginalGenuineResourcesData
  refine ⟨fun q r a k => (hgrid q r a).period_pos k, ?_⟩
  intro w v Pfinal Mk hMk selection hqDim hcard _ hMkPsp hlarge hG hdimP hDexp
    hpAccuracy he hE hcgeom hO hpc hgc hPτ hδ hδ1 hδe hKgen hSampling Kernel Good GoodKernel
  obtain ⟨d, hd, hdb, modulus, hmodulus, hmodulusSize, hspatial, hcoefficient, hcoarse⟩ :=
    hcoarse selection hqDim hcard hMkPsp hlarge
  let _ : ∀ x, NeZero (d x) := fun x => ⟨(hd x).ne'⟩
  let _ : ∀ x, NeZero (modulus x) := fun x => ⟨(hmodulus x).ne'⟩
  refine ⟨d, hd, hdb, modulus, hmodulus, hmodulusSize, hspatial, hcoefficient, ?_⟩
  intro block _ _ _ _ _ _ hb o Kcov _ bW C V hC hV hCp hVp hCpAccuracy hVpAccuracy
    Cinv hCinv hchart hgeom hvars hIgeom hngeom hKcov hCgeom hsmall hRadius hCovEarly hσ1
    μ _ _ ν _ _ _ _ _ μsmall _ _ X _ _ hXPsp q hq hqPsp refined index _
    W hW indices ξ hξ mesh τ hτ hτP hτEarly hτ1 Psrc Psamp hnum hPsamp hdimPsamp hτPsamp
    N hN hsizeN hsizeBox hsizeG poly hpoly hmem rank hrank hRank hRankG cells hcells
    bases hbases hbaseBox V₀ Z law wholeReference idealLog
  have hphysical (j : Fin m) : R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cinv 1 j :=
    (hsmall j).trans (allocatedProductChartRadius_le_charts B rowSets hgeom hcgeom
      hIgeom hngeom Cinv hCinv hCgeom j).2.1
  have hproduct (j : Fin m) : R j ≤ allocatedProductGridRadius (G := G) B rowSets Cinv j :=
    (hsmall j).trans (allocatedProductChartRadius_le_charts B rowSets hgeom hcgeom
      hIgeom hngeom Cinv hCinv hCgeom j).1
  obtain ⟨hmass, hZ, _⟩ := hcoarse block hb o bW C V hC hV hCp hVp hCpAccuracy hVpAccuracy
    Cinv hCinv hchart hphysical hσ1 hproduct μ ν μsmall hXPsp q hq hqPsp hτ hτP hτ1
    N hN hsizeN hsizeBox poly hpoly hmem hrank hRank cells hcells
    (fun _ _ => 0) (by intros; simp) bases hbases hbaseBox
  have hw : 0 ≤ w := allocatedSiteKernelMaskLog_nonneg m hP
  have hv : 0 ≤ v := allocatedIdealProfileLog_nonneg m hpAccuracy he
  have hPsamp0 : 0 ≤ Psamp := hP.trans hPsamp
  have hone : (1 : ℝ) ≤ Real.exp Psamp := Real.one_le_exp_iff.mpr hPsamp0
  have hstride (z : X) : (q z : ℝ) ≤ Real.exp Psamp :=
    (hqPsp z).trans (Real.exp_le_exp.mpr hPsamp)
  have hfamily (x : GoodKernel) (base : X → ℤ) :=
    exists_allocated_coarse_genuine_source_comparison
      (B := B) (U := U) (b := b) (hR := hR) (hσ := hσ) (hσ1 := hσ1) (S := S)
      (X := X) (modulus := modulus x) (q := q) (wholeReference := wholeReference x)
      (coverWitness := witnesses (index x)) (hb := hb) (o := o) (bW := bW) (d := d x)
      (δ := δ) (x := x.val) (hM := hMk) (selection := selection) (hx := x.property)
      (pAccuracy := pAccuracy) (w := w) (v := v) (Ecoarse := E + 2)
      (N := N) (base := base) (cells := cells) (p := poly) (hm := hmem)
      (C := Cinv) (hC := hCinv) (hchart := hchart) (hgeom := hgeom) (hcgeom := hcgeom)
      (hIgeom := hIgeom) (hngeom := hngeom) (hCgeom := hCgeom) (hsmall := hsmall)
      (D := C) (hD := hC) (Vcov := V) (hnum := hnum) (hVcov := fun j => (hV j).2)
      (Psp := Psp) (O := O) (E := E) (Z := Z) (P := Psamp) (Elog := 0)
      (εs := 1) (η := 1) (S₀ := Real.exp Psamp)
      hpAccuracy hw hv (by linarith) hG (hmodulusSize x)
      hP hDexp hdimP hXPsp hvars hKcov hO hE hMkPsp hZ.2.2.1 hZ.2.2.2
      (hgrid (index x)) hKgen hSampling hPsamp0 (hXPsp.trans hPsamp) hdimPsamp μsmall ν
      (Real.exp_pos _).le le_rfl (by norm_num) hτPsamp (by simpa using hone) hstride
      hsizeG hrank hRankG (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num)
      hq hτ (hspatial x (fun g => (0 : ℤ) + (x.val g none : ℤ))) hpoly hqDim hδ hδ1 hξ he hδe hmass
  choose t ht F hF happrox using hfamily
  have hDgeom : 0 ≤ Dgeom := by
    obtain ⟨hD, _⟩ := hgeom
    exact hD
  have hlog : 0 ≤ idealLog := allocatedGenuineComparisonErrorLog_nonneg m hP hDgeom hcgeom
    (coarseSpatialLogs_nonneg (allocatedProductCoarseInput_nonneg m dim hP hpAccuracy hw hv
      (by linarith : 0 ≤ E + 2))).2 hO hE
  have hpI := (allocatedFiniteIdealInputLog_bounds m hDgeom he hlog).1
  refine ⟨hmass, hZ, t, ht, F, hF, ?_, ?_⟩
  · intro x base gridPeriod
    exact allocatedCoarseFamilyResources_of_bounds
      (B := B) (U := U) (b := b) (S := S) (X := X) (modulus := modulus x) (q := q)
      (wholeReference := wholeReference x) (coverWitness := witnesses (index x))
      (hb := hb) (o := o) (bW := bW) (d := d x) (hR := hR) (x := x.val)
      (hM := hMk) (selection := selection) (hx := x.property) (N := N) (τ := τ)
      (period := kernelPeriodCandidate (m + 1) (t x base)) (F := F x base) (base := base)
      (hF x base) (hgrid (index x)) hpI hP hpAccuracy hw hv (by linarith) hO hpc hgc hPτ
      (by convert hgeom using 1)
      hngeom hKcov hvars hqDim hG hXPsp hMkPsp (hmodulusSize x) (ht x base)
      hq hN hτ hRadius hCovEarly hqPsp hτEarly hZ.2.2.1 hZ.2.2.2
      (hspatial x (fun g => (0 : ℤ) + (x.val g none : ℤ)))
  · intro test htest genuine window hwindow hDwindow shift moduli residues hmoduli hmoduliM kernelLaw
    obtain ⟨hmass', _, hsource⟩ := hcoarse block hb o bW C V hC hV hCp hVp hCpAccuracy hVpAccuracy
      Cinv hCinv hchart hphysical hσ1 hproduct μ ν μsmall hXPsp q hq hqPsp hτ hτP hτ1
      N hN hsizeN hsizeBox poly hpoly hmem hrank hRank cells hcells test htest bases hbases hbaseBox
    have hsourceLaw := hsource window hwindow hDwindow shift moduli residues hmoduli hmoduliM
    let cover : GoodKernel → (X → ℤ) → ℂ := fun x base =>
      (law.fiberLaw (principalResidueLabel (refined x))).complexMean (fun r =>
        ∑ a : cells, (selectedResidueCellWeight q cells V₀ a : ℂ) *
          ∑ z ∈ spatialWindow (trimmedSpatialRootScale τ N q) 4,
            allocatedRecenteredResidueWeight (τ := τ) B U b S X (modulus x) q (wholeReference x)
              x.val hMk selection x.property N hW (mesh x) base cells
              (physicalCubeSiteTest (fun site => integerBoxTestExtension N (test site))) r a z *
            allocatedProductFullGridResidueProfile B U b hR hσ S (refined x) x.val hb o bW (d x)
              (witnesses (index x)) δ r (physicalCubeRowSample (O := fun j => (rowSets j : Type))
                U (d x) fullRows poly hmem
                (allocatedWholeResidueReconstruction B U b S X (modulus x) q (wholeReference x)
                  x.val base r a.val z))) / (Z : ℂ)
    have hpoint (x : Kernel) (hx : Good x) (base : X → ℤ) (_hb : base ∈ bases) :
        ‖cover ⟨x, hx⟩ base - genuine ⟨x, hx⟩ base‖ ≤ Real.exp (-E) :=
      happrox ⟨x, hx⟩ base test htest
    have htransfer := kernelLaw.complexMean_goodPart_base_transfer bases hbases Good
      (fun x base => allocatedOriginalTupleSource B U b hR hσ S x X q hb o N hN hW hτ hξ
        base cells hmass (physicalCubeSiteTest test) Z poly hmem)
      (fun x hx base => cover ⟨x, hx⟩ base) (fun x hx base => genuine ⟨x, hx⟩ base)
      (Real.exp_pos (-E)).le hsourceLaw hpoint
    exact htransfer.trans_eq (by ring)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {p cEarly cLate P e E : ℝ}

local notation "Eraw" => (E + 2) + 4

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "accuracy" => allocatedOriginalCoverAccuracy P (E + 2)
local notation "pAccuracy" => allocatedCommonRefinedSourceLog m p cEarly P e 0 accuracy
local notation "pSampling" => allocatedCommonRefinedSourceLog m p cLate P e Eraw accuracy
local notation "S" => allocatedCommonScale (G := G) B U b hR hσ p cLate P e Eraw
local notation "maskLog" => allocatedSiteKernelMaskLog m P
local notation "profileLog" => allocatedIdealProfileLog m pAccuracy e
local notation "resourceLog" => allocatedFullGridPrimitiveResourceLog m pAccuracy maskLog profileLog accuracy
local notation "tolerance" => allocatedSitePrimitiveTolerance m pAccuracy maskLog profileLog accuracy

local notation "D" => allocatedComparisonDimension m p
local notation "pNum" => allocatedCommonScaleNumeric m p cLate P Eraw
local notation "error" => allocatedReferenceIdealError m D P Eraw
local notation "lengthLog" => allocatedIdealScaleLog m D pNum e maskLog error
local notation "gainLog" => allocatedProfileGainLog m D P maskLog
local notation "Pbase" => allocatedIdealSourceBudget m D pNum e maskLog error
local notation "lateLog" => allocatedSpatialLateLog (G := G) B Pbase Pbase
local notation "rawFourier" => allocatedProfileFourierOutput (allocatedActualProfileInput m D pNum e gainLog lengthLog)
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

theorem exists_original_common_genuine_resource_source
    (hp : 0 ≤ p) (hcEarly : 0 ≤ cEarly) (hcLate : 0 ≤ cLate) (hEarlyLate : cEarly ≤ cLate)
    (hP : 0 ≤ P) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hdimSmall : dim ≤ m + 1) (hmP : ((m + 2 : ℕ) : ℝ) ≤ P) (hpP : p ≤ P)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ 2 * p)
    (hR1 : ∀ j, R j ≤ 1) (hσ1 : ∀ j, σ j ≤ 1)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp cEarly) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp cLate)
    (hBlocks : ∀ (j : Fin m) (i : Fin (n j)), max
      (positiveModerateSpectrumBlockCount j.val (rowSets j).card
        ((layerTailDegree m + 2) * (rowSets j).card))
      (uniformSpectrumBlockCount j.val (rowSets j).card ((j.val + 1) * (rowSets j).card)) ≤
      Fintype.card (B ⟨j, Sum.inr i⟩))
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδe : (δ : ℝ)⁻¹ ≤ Real.exp e)
    {A T Kproj Kideal Ksite Knorm : ℕ} (hT : 1 ≤ T) (hKsite : 2 ≤ Ksite)
    (hKnorm : 1 ≤ Knorm)
    (hnorm : AllocatedSourceNarrowNormalization.{uG,uI,uB,uJ,uX} m Knorm)
    (hSampling : AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim Ksite rowTypes rows)
    (hraw : AllocatedOriginalResidueWeightedMeshAtScale.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B U b hR hσ D P (E + 2) e pNum δ A T Kproj Kideal) :
    ∃ witnesses : (q : AllocatedRefinedPeriodIndex m P) →
        (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
        AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val,
      (∀ q r a, ((witnesses q r).expansion a).Bounds
        (Real.exp resourceLog) (Real.exp resourceLog) (Real.exp resourceLog)
        ⟨Real.exp resourceLog, Real.exp_nonneg _⟩
        (Real.exp (allocatedInactiveSupportLog (allocatedComparisonDimension m pAccuracy)))) ∧
      (∀ q r, AllocatedFullGridResidueSampling.{uG,uI,uB,uJ,uQ,uX}
        B U b hR hσ S (q.val : ℕ) (witnesses q r) tolerance) ∧
      ∀ (Dgeom cgeom pc gc Pτ : ℝ) (Kgen : ℕ) (M Dwin : ℕ) (hM : 0 < M) (hDwin : 0 < Dwin) (η : ℝ) (hη : 0 < η),
        AllocatedOriginalGenuineResourcesData.{uG,uI,uB,uJ,uQ,uX}
          B U b hR hσ S P E e pNum Pbase
          (allocatedSourceSamplingBudget m dim A Pbase (E + 2) lateLog rawFourier)
          pAccuracy pSampling Dgeom cgeom resourceLog pc gc Pτ hP δ A
          (max T (max Kproj Kideal)) (max Ksite Knorm) Kgen witnesses
          M Dwin hM hDwin η hη := by
  obtain ⟨witnesses, hBounds, hWitnesses, hData⟩ :=
    exists_original_common_coarse_box_source B U b hR hσ hp hcEarly hcLate hEarlyLate hP he hE
      hdimSmall hmP hpP hvars hI hn hJ hR1 hσ1 hRi hσi hBlocks hδ hδ1 hδe
      hT hKsite hKnorm hnorm hSampling hraw
  refine ⟨witnesses, hBounds, hWitnesses, ?_⟩
  intro Dgeom cgeom pc gc Pτ Kgen M Dwin hM hDwin η hη
  exact allocatedOriginalGenuineResourcesData_of_coarse B U b hR hσ S hP witnesses hBounds
    M Dwin hM hDwin η hη (hData M Dwin hM hDwin η hη)

end Erdos3.VectorPolynomial

end

end OAI
