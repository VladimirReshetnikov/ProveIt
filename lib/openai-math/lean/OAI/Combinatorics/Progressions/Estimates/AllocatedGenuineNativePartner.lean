import OAI.Combinatorics.Progressions.Geometry.AllocatedGenuineSpatialReindex
import OAI.Combinatorics.Progressions.Polynomial.CubeMixtureAllDegrees

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ i, Fintype (B i)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (coverWitness : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S (residueRefinedPeriod modulus q) r.val)
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (N : X → ℕ) {τ : ℝ} (mesh : ℝ≥0) (base : X → ℤ)
variable (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q))
variable (a : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q)
variable (spatial : X → SpatialSiteLabel (Fin dim) modulus 4 mesh)
variable (kg : ∀ i, ((coverWitness r).expansion i).Term)
variable (fi : (LayerSamplerAxis I n → ℝ) → ℂ) (s : Finset (Fin dim))
variable (gridLabel : ∀ i, ZMod (((coverWitness r).expansion i).period (kg i)))

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "radius" => allocatedProductIdealSiteRadius (G := G) B rowSets
local notation "positiveRadius" => allocatedProductIdealSiteRadius_pos (G := G) B rowSets
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "expansion" => AllocatedFullGridResidueWitness.expansion (coverWitness r)
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (wholeReference r.val)
local notation "directions" => allocatedPhysicalCubeDirections B U b S x (wholeReference r.val)
local notation "residue" => boundedColumnResidueRepresentative q a

noncomputable def allocatedRecenteredContinuousSiteFactor :
    ((X → ℝ) × (LayerSamplerAxis I n → ℝ)) → ℂ :=
  normalizedSiteTwistProduct
    (physicalResidueSpatialSmooth root directions base residue q 4 mesh
      (trimmedSpatialRootScale τ N q) (fun z => (N z : ℝ)) spatial s)
    (allocatedNormalizedGridIdealFactor B U b S expansion ig radius positiveRadius kg s gridLabel fi)

theorem nonneg_exp_sum_le_exp_add_one {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Real.exp A + Real.exp B ≤ Real.exp (A + B + 1) := by
  have ha : Real.exp A ≤ Real.exp (A + B) := Real.exp_le_exp.mpr (by linarith only [hB])
  have hb : Real.exp B ≤ Real.exp (A + B) := Real.exp_le_exp.mpr (by linarith only [hA])
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ 2 * Real.exp (A + B) := by linarith only [ha, hb]
    _ ≤ Real.exp 1 * Real.exp (A + B) := mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem allocatedRecenteredContinuousSiteFactor_pre_bounds
    (hR : ∀ j, 0 < R j)
    {T Vg Cg Hg : {i // allocatedGridAxis (I := I) U b S.value i} → ℝ} {L LI : ℝ≥0}
    (he : ∀ i, ((coverWitness r).expansion i).Bounds (T i) (Vg i) (Cg i) L (Hg i))
    (Q : ℝ≥0) (hQ : ∀ i, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (ig i).1 (ig i).2) : ℝ) + 1) ≤ Q)
    (hf : ∀ y, ‖fi y‖ ≤ 1)
    (hI : LipschitzWith LI (bufferedCoordinateProjection
      (allocatedGridAxis (I := I) U b S.value) radius positiveRadius fi))
    (hmesh : 0 < mesh) (hq : ∀ z, 0 < q z) (hN : ∀ z, 0 < N z) (hτ : 0 < τ)
    {D eL eQ eI Pmesh EX ES Pτ : ℝ}
    (hD : 0 ≤ D) (heL : 0 ≤ eL) (heQ : 0 ≤ eQ) (heI : 0 ≤ eI)
    (hPmesh : 0 ≤ Pmesh) (hEX : 0 ≤ EX) (hES : 0 ≤ ES) (hPτ : 0 ≤ Pτ)
    (haxes : (Fintype.card {i // allocatedGridAxis (I := I) U b S.value i} : ℝ) ≤ D)
    (hL : (L : ℝ) ≤ Real.exp eL) (hQexp : (Q : ℝ) ≤ Real.exp eQ) (hIexp : (LI : ℝ) ≤ Real.exp eI)
    (hbox : (4 : ℝ) ≤ Real.exp Pmesh) (hinv : 1 / (mesh : ℝ) ≤ Real.exp Pmesh)
    (hX : (Fintype.card X : ℝ) ≤ Real.exp EX)
    (hS : (Fintype.card (Unit ⊕ Fin dim) : ℝ) ≤ Real.exp ES)
    (hτexp : 1 / τ ≤ Real.exp Pτ) :
    (∀ v, ‖allocatedRecenteredContinuousSiteFactor (τ := τ) B U b S X modulus q wholeReference
      coverWitness x N mesh base r a spatial kg fi s gridLabel v‖ ≤ 1) ∧
    LipschitzWith
      ⟨Real.exp (ES + EX + (3 * Pmesh + 6) + (Pτ + 8) + (D + eL + eQ + eI + 1) + 1),
        Real.exp_nonneg _⟩
      (allocatedRecenteredContinuousSiteFactor (τ := τ) B U b S X modulus q wholeReference
        coverWitness x N mesh base r a spatial kg fi s gridLabel) := by
  let Lscale : ℝ≥0 := ⟨8 / τ, div_nonneg (by norm_num) hτ.le⟩
  have hscale (z : X) : |(N z : ℝ) / ((q z : ℝ) * trimmedSpatialRootScale τ N q z)| ≤ Lscale := by
    rw [trimmedSpatialRootScale_normalized_ratio N q hτ hN hq z]
    exact (abs_of_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 8) hτ.le)).le
  have hscaleExp : (Lscale : ℝ) ≤ Real.exp (Pτ + 8) := by
    change 8 / τ ≤ _
    calc
      _ = 8 * (1 / τ) := by ring
      _ ≤ 8 * Real.exp Pτ := mul_le_mul_of_nonneg_left hτexp (by norm_num)
      _ ≤ Real.exp 8 * Real.exp Pτ := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (8 : ℝ)] : (8 : ℝ) ≤ Real.exp 8) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hsp := physicalResidueSpatialSmooth_bounds root directions base residue q 4 mesh
    (trimmedSpatialRootScale τ N q) (fun z => (N z : ℝ)) spatial s hmesh hscale
  have hspL := physicalResidueSpatialSmooth_pre_lipschitz root directions base residue q 4 mesh
    (trimmedSpatialRootScale τ N q) (fun z => (N z : ℝ)) spatial s hmesh hscale
    hPmesh (by norm_num) hbox hinv hX hS hscaleExp
  have hgrid := allocatedNormalizedGridIdealFactor_bounds B U b S expansion ig radius positiveRadius
    kg s gridLabel fi hR he Q hQ hf hI
  have hgridL := allocatedNormalizedGridIdealFactor_pre_lipschitz B U b S expansion ig radius positiveRadius
    kg s gridLabel fi hR he Q hQ hf hI hD heL heQ heI haxes hL hQexp hIexp
  have hprod := normalizedSiteTwistProduct_bounds _ _ hspL hgridL hsp.1 hgrid.1
  refine ⟨hprod.1, hprod.2.weaken ?_⟩
  apply NNReal.coe_le_coe.mp
  exact nonneg_exp_sum_le_exp_add_one (by positivity) (by positivity)

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)
variable (period : ℕ)
variable (label : (∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period))

local notation "common" => siteTwistCommonModulus modulus q expansion kg period

theorem allocatedRecenteredNormalizedSiteFactor_continuous (u : X → ℤ) :
    allocatedRecenteredNormalizedSiteFactor (τ := τ) B U b S X modulus q wholeReference coverWitness
      hb o bW d x N mesh base p hm r a period spatial kg label fi s gridLabel u =
    restrictedComplexChartDensity (mixedCoveredJetChart (O := fun _ => Unit) U o b hb bW d)
      (mixedCoveredJetRegion U o b d (fun j (_ : Unit) => standardLatticeSmallBox (J j))) 1
      (fun w =>
        allocatedCommonResidueMask expansion kg ig root directions base residue q 4 mesh
          (siteTwistCommonModulus_spatial_dvd modulus q expansion kg period)
          (siteTwistCommonModulus_grid_dvd modulus q expansion kg period)
          (siteTwistCommonModulus_ideal_dvd modulus q expansion kg period)
          spatial s label gridLabel (fun z => (u z : ZMod common)) (mixedCoveredSiteResidue d common w) *
        allocatedRecenteredContinuousSiteFactor (τ := τ) B U b S X modulus q wholeReference
          coverWitness x N mesh base r a spatial kg fi s gridLabel
          ((fun z => (u z : ℝ) / N z), allocatedFullMixedSiteValue (R := R) U b
            (fun j => mixedArrayRegroup (I j) (Fin (n j)) Unit (w.1 j) ())))
      (physicalSingleSiteValue U d p hm (fun z => (u z : ℝ))) := by
  rfl

theorem allocatedRecenteredNormalizedSiteFactor_norm_le
    (hf : ∀ v, ‖allocatedRecenteredContinuousSiteFactor (τ := τ) B U b S X modulus q
      wholeReference coverWitness x N mesh base r a spatial kg fi s gridLabel v‖ ≤ 1)
    (u : X → ℤ) :
    ‖allocatedRecenteredNormalizedSiteFactor (τ := τ) B U b S X modulus q wholeReference coverWitness
      hb o bW d x N mesh base p hm r a period spatial kg label fi s gridLabel u‖ ≤ 1 := by
  rw [allocatedRecenteredNormalizedSiteFactor_continuous]
  apply restrictedComplexChartDensity_norm_le _ _
    (mixedCoveredJetChart_injOn U o b hb bW d _ (fun _ _ => Set.Subset.rfl)) _ zero_le_one
  intro w
  rw [norm_mul]
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hf _)
  exact allocatedCommonResidueMask_norm expansion kg ig root directions base residue q 4 mesh
    (siteTwistCommonModulus_spatial_dvd modulus q expansion kg period)
    (siteTwistCommonModulus_grid_dvd modulus q expansion kg period)
    (siteTwistCommonModulus_ideal_dvd modulus q expansion kg period)
    spatial s label gridLabel _ _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (coverWitness : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S (residueRefinedPeriod modulus q) r.val)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (g : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  (∀ a, ((coverWitness r).expansion a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ))
variable (δ : ℝ≥0) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ : ℝ} (hW : 0 ≤ W) (mesh : ℝ≥0) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)
variable (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) (a : cells)

local notation "refined" => residueRefinedPeriod modulus q
local notation "terms" => (X → SpatialSiteLabel (Fin dim) modulus 4 mesh)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "point" => allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base r.val a.val
local notation "volume" => ∏ z, ∏ i, physicalSpatialOutputScale (Fin dim)
  (trimmedSpatialRootScale τ N q z) (trimmedSpatialSlopeScale W τ N q z) S.value i
local notation "coeff" => allocatedSpatialExpansionCoefficient B U b S x X hM selection hx modulus hW mesh
local notation "twist" => allocatedRecenteredSpatialTwist (τ := τ) B U b S X modulus q wholeReference x N mesh base

variable (period : ℕ) [NeZero period]
variable {K : Type*} [Fintype K] (cI : K → ℂ)
variable (fI : K → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)

local notation "radius" => allocatedProductIdealSiteRadius (G := G) B rowSets
local notation "positiveRadius" => allocatedProductIdealSiteRadius_pos (G := G) B rowSets

variable [∀ (i : {i // allocatedGridAxis (I := I) U b S.value i})
  (ki : ((coverWitness r).expansion i).Term), NeZero (((coverWitness r).expansion i).period ki)]

local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "ambient" => allocatedAmbientNormalizedSpatialApproximation (τ := τ) B U b S X modulus q
  wholeReference coverWitness hb o bW d x hM selection hx N hW mesh base cells p hm r a period cI fI
local notation "recentered" => allocatedRecenteredNormalizedSpatialApproximation (τ := τ) B U b S X modulus q
  wholeReference coverWitness hb o bW d x hM selection hx N hW mesh base cells p hm r a period cI fI

theorem allocated_genuine_cube_expansion [DecidableEq X]
    (hunit : ∀ spatial kg k s gridLabel z,
      ‖allocatedRecenteredContinuousSiteFactor (τ := τ) B U b S X modulus q wholeReference
        coverWitness x N mesh base r a.val spatial kg (fI k s) s gridLabel z‖ ≤ 1) :
    let Index := Σ t : terms × (∀ i, ((coverWitness r).expansion i).Term),
      (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period))) ×
        K × (Finset (Fin dim) → ∀ i, ZMod (((coverWitness r).expansion i).period (t.2 i)))
    letI : Fintype Index := by
      letI : Fintype (terms × (∀ i, ((coverWitness r).expansion i).Term)) := inferInstance
      letI : ∀ t : terms × (∀ i, ((coverWitness r).expansion i).Term),
          Fintype ((Finset (Fin dim) →
            ((∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period))) ×
            K × (Finset (Fin dim) → ∀ i,
              ZMod (((coverWitness r).expansion i).period (t.2 i)))) := fun t => inferInstance
      dsimp only [Index]
      infer_instance
    let raw := fun t label k =>
      (coeff (principalResidueLabel modulus (wholeReference r.val)) t.1 / ((volume : ℝ) : ℂ)) *
        coverSiteCoefficient (coverWitness r).expansion t.2 *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x
          (coverWitness r).representative refined d period cI label k
    let c : Index → ℂ := fun i => (integerBoxCubeCount N dim : ℂ) * raw i.1 i.2.1 i.2.2.1
    let Ψ : Index → Finset (Fin dim) → (X → ℤ) → ℂ := fun i s u =>
      allocatedRecenteredNormalizedSiteFactor (τ := τ) B U b S X modulus q wholeReference coverWitness
        hb o bW d x N mesh base p hm r a.val period i.1.1 i.1.2 (i.2.1 s) (fI i.2.2.1 s) s
        (i.2.2.2 s) u
    (∀ i s u, ‖Ψ i s u‖ ≤ 1) ∧
    (∑ i, ‖c i‖) = (integerBoxCubeCount N dim : ℝ) *
      ∑ t : terms × (∀ i, ((coverWitness r).expansion i).Term),
        ∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period)),
          ∑ k : K,
            ∑ _gridLabel : Finset (Fin dim) → ∀ i, ZMod (((coverWitness r).expansion i).period (t.2 i)),
              ‖raw t label k‖ ∧
    ∀ test : Finset (Fin dim) → (X → ℝ) → ℂ,
      (integerBoxCubeCount N dim : ℂ) *
        (𝔼 cube : SupportedCube dim (integerBox N : Set (X → ℤ)),
          ambient test ((physicalCubeParametersEquiv X dim).symm cube.val)) =
        ∑ i, c i * (𝔼 cube : SupportedCube dim (integerBox N : Set (X → ℤ)),
          let u := (physicalCubeParametersEquiv X dim).symm cube.val
          ∏ s, test s (fun z => (physicalCubeVertexValue u s z : ℝ)) *
            Ψ i s (physicalCubeVertexValue u s)) := by
  intro Index raw c Ψ
  refine ⟨?_, ?_, ?_⟩
  · intro i s u
    exact allocatedRecenteredNormalizedSiteFactor_norm_le B U b S X modulus q wholeReference
      coverWitness x N mesh base r a.val i.1.1 i.1.2 (fI i.2.2.1 s) s (i.2.2.2 s)
      hb o bW d p hm period (i.2.1 s) (hunit _ _ _ _ _) u
  · simp only [Index, c, Fintype.sum_sigma, Fintype.sum_prod_type, norm_mul,
      Complex.norm_natCast, Finset.mul_sum]
  · intro test
    simpa only [Index, c, Ψ, raw, Fintype.sum_sigma, Fintype.sum_prod_type] using
      allocatedAmbientNormalizedSpatialApproximation_mixture B U b S X modulus q wholeReference
        coverWitness hb o bW d x hM selection hx N hW mesh base cells p hm r a period cI fI test

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq fullBooleanRowSetFintype

variable {m s nX : ℕ}
variable {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (modulus : ℕ) [NeZero modulus] (q : (Fin nX) → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U b S))
variable (coverWitness : (r : AllocatedPositiveResidue (dim := (s + 1)) B U b S (residueRefinedPeriod modulus q)) →
  AllocatedFullGridResidueWitness (dim := (s + 1)) B U b S (residueRefinedPeriod modulus q) r.val)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (g : (r : AllocatedPositiveResidue (dim := (s + 1)) B U b S (residueRefinedPeriod modulus q)) →
  (∀ a, ((coverWitness r).expansion a).Term) → Finset (Fin (s + 1)) → (((Σ j, J j) → UnitAddCircle) → ℂ))
variable (δ : ℝ≥0) (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin (s + 1) ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : (Fin nX) → ℕ) {W τ : ℝ} (hW : 0 ≤ W) (mesh : ℝ≥0) (base : (Fin nX) → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) q))
variable (p : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)
variable (r : AllocatedPositiveResidue (dim := (s + 1)) B U b S (residueRefinedPeriod modulus q)) (a : cells)

local notation "refined" => residueRefinedPeriod modulus q
local notation "terms" => ((Fin nX) → SpatialSiteLabel (Fin (s + 1)) modulus 4 mesh)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin (s + 1))))
local notation "point" => allocatedWholeResidueReconstruction B U b S (Fin nX) modulus q wholeReference x base r.val a.val
local notation "volume" => ∏ z, ∏ i, physicalSpatialOutputScale (Fin (s + 1))
  (trimmedSpatialRootScale τ N q z) (trimmedSpatialSlopeScale W τ N q z) S.value i
local notation "coeff" => allocatedSpatialExpansionCoefficient B U b S x (Fin nX) hM selection hx modulus hW mesh
local notation "twist" => allocatedRecenteredSpatialTwist (τ := τ) B U b S (Fin nX) modulus q wholeReference x N mesh base

variable (period : ℕ) [NeZero period]
variable {K : Type} [Fintype K] (cI : K → ℂ)
variable (fI : K → Finset (Fin (s + 1)) → (LayerSamplerAxis I n → ℝ) → ℂ)

local notation "radius" => allocatedProductIdealSiteRadius (G := G) B rowSets
local notation "positiveRadius" => allocatedProductIdealSiteRadius_pos (G := G) B rowSets

variable [∀ (i : {i // allocatedGridAxis (I := I) U b S.value i})
  (ki : ((coverWitness r).expansion i).Term), NeZero (((coverWitness r).expansion i).period ki)]

local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "ambient" => allocatedAmbientNormalizedSpatialApproximation (τ := τ) B U b S (Fin nX) modulus q
  wholeReference coverWitness hb o bW d x hM selection hx N hW mesh base cells p hm r a period cI fI
local notation "recentered" => allocatedRecenteredNormalizedSpatialApproximation (τ := τ) B U b S (Fin nX) modulus q
  wholeReference coverWitness hb o bW d x hM selection hx N hW mesh base cells p hm r a period cI fI

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem allocated_genuine_cube_native_partner [∀ z, NeZero (N z)]
    (hunit : ∀ spatial kg k site gridLabel z,
      ‖allocatedRecenteredContinuousSiteFactor (τ := τ) B U b S (Fin nX) modulus q wholeReference
        coverWitness x N mesh base r a.val spatial kg (fI k site) site gridLabel z‖ ≤ 1)
    {budget Z : ℝ} (hbudget : 0 ≤ budget) (hdimension : (nX : ℝ) ≤ budget) (hZ : 0 < Z)
    (hmass : (integerBoxCubeCount N (s + 1) : ℝ) *
      (∑ t : terms × (∀ i, ((coverWitness r).expansion i).Term),
        ∑ label : Finset (Fin (s + 1)) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period)),
          ∑ k : K,
            ∑ _gridLabel : Finset (Fin (s + 1)) → ∀ i, ZMod (((coverWitness r).expansion i).period (t.2 i)),
              ‖(coeff (principalResidueLabel modulus (wholeReference r.val)) t.1 / ((volume : ℝ) : ℂ)) *
                coverSiteCoefficient (coverWitness r).expansion t.2 *
                allocatedProductMaskedIdealCoefficient B U b S rowSets x
                  (coverWitness r).representative refined d period cI label k‖) / Z ≤ Real.exp budget)
    (f : ((Fin nX) → ℤ) → ℂ) (hf : ∀ u ∈ integerBox N, ‖f u‖ ≤ 1)
    (hpositive : Real.exp (-budget) ≤
      (((integerBoxCubeCount N (s + 1) : ℂ) *
        (𝔼 cube : SupportedCube (s + 1) (integerBox N : Set ((Fin nX) → ℤ)),
          ambient (fun site y => conjugationPower site.card (f (fun z => ⌊y z⌋)))
            ((physicalCubeParametersEquiv (Fin nX) (s + 1)).symm cube.val))) / (Z : ℂ)).re) :
    ∃ (spatial : terms) (kg : ∀ i, ((coverWitness r).expansion i).Term)
      (label : (∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period))
      (k : K) (gridLabel : ∀ i, ZMod (((coverWitness r).expansion i).period (kg i)))
      (V : NativeSampleCorrelation (fun _ : (Fin nX) => 1) s
        ((budget + 2) ^ Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s))
        (integerBox N) id
        (fun u => f u * allocatedRecenteredNormalizedSiteFactor (τ := τ) B U b S (Fin nX) modulus q
          wholeReference coverWitness hb o bW d x N mesh base p hm r a.val period
          spatial kg label (fI k ∅) ∅ gridLabel u)),
      V.test.normBound ≤ 1 := by
  let Index := Σ t : terms × (∀ i, ((coverWitness r).expansion i).Term),
    (Finset (Fin (s + 1)) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period))) ×
      K × (Finset (Fin (s + 1)) → ∀ i, ZMod (((coverWitness r).expansion i).period (t.2 i)))
  let : Fintype Index := by
    letI : Fintype (terms × (∀ i, ((coverWitness r).expansion i).Term)) := inferInstance
    letI : ∀ t : terms × (∀ i, ((coverWitness r).expansion i).Term),
        Fintype ((Finset (Fin (s + 1)) →
          ((∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period))) ×
          K × (Finset (Fin (s + 1)) → ∀ i,
            ZMod (((coverWitness r).expansion i).period (t.2 i)))) := fun t => inferInstance
    dsimp only [Index]
    infer_instance
  let raw := fun (t : terms × (∀ i, ((coverWitness r).expansion i).Term))
      (label : Finset (Fin (s + 1)) →
        ((∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period))) (k : K) =>
    (coeff (principalResidueLabel modulus (wholeReference r.val)) t.1 / ((volume : ℝ) : ℂ)) *
      coverSiteCoefficient (coverWitness r).expansion t.2 *
      allocatedProductMaskedIdealCoefficient B U b S rowSets x
        (coverWitness r).representative refined d period cI label k
  let c : Index → ℂ := fun i => (integerBoxCubeCount N (s + 1) : ℂ) * raw i.1 i.2.1 i.2.2.1
  let Ψ : Index → Finset (Fin (s + 1)) → ((Fin nX) → ℤ) → ℂ := fun i s u =>
    allocatedRecenteredNormalizedSiteFactor (τ := τ) B U b S (Fin nX) modulus q wholeReference coverWitness
      hb o bW d x N mesh base p hm r a.val period i.1.1 i.1.2 (i.2.1 s) (fI i.2.2.1 s) s
      (i.2.2.2 s) u
  have hexp := allocated_genuine_cube_expansion B U b S (Fin nX) modulus q wholeReference
    coverWitness hb o bW d x hM selection hx N hW mesh base cells p hm r a period cI fI hunit
  change (∀ i site u, ‖Ψ i site u‖ ≤ 1) ∧
    (∑ i, ‖c i‖) = _ ∧ _ at hexp
  rcases hexp with ⟨hΨ, hcoeff, hexp⟩
  let normalized : Index → ℂ := fun i => c i / (Z : ℂ)
  have hnormalized : (∑ i, ‖normalized i‖) ≤ Real.exp budget := by
    simp only [normalized, norm_div, Complex.norm_real, Real.norm_of_nonneg hZ.le,
      ← Finset.sum_div, hcoeff]
    exact hmass
  let test : Finset (Fin (s + 1)) → ((Fin nX) → ℝ) → ℂ :=
    fun site y => conjugationPower site.card (f (fun z => ⌊y z⌋))
  have hvalue := hexp test
  simp only [test, Int.floor_intCast] at hvalue
  let z : ℂ := ((integerBoxCubeCount N (s + 1) : ℂ) *
    (𝔼 cube : SupportedCube (s + 1) (integerBox N : Set ((Fin nX) → ℤ)),
      ambient test ((physicalCubeParametersEquiv (Fin nX) (s + 1)).symm cube.val))) / (Z : ℂ)
  have herr : ‖z - ∑ i, normalized i *
      (𝔼 cube : SupportedCube (s + 1) (integerBox N : Set ((Fin nX) → ℤ)),
        let u := (physicalCubeParametersEquiv (Fin nX) (s + 1)).symm cube.val
        ∏ site, conjugationPower site.card (f (physicalCubeVertexValue u site)) *
          Ψ i site (physicalCubeVertexValue u site))‖ ≤ Real.exp (-budget) / 2 := by
    dsimp only [z]
    rw [hvalue]
    simp only [normalized, c, raw, Ψ, div_mul_eq_mul_div, ← Finset.sum_div]
    refine (le_of_eq ?_).trans (half_pos (Real.exp_pos (-budget))).le
    rw [norm_eq_zero, sub_eq_zero]
  obtain ⟨i, V, hV, _⟩ := (Classical.choose_spec
    (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s)).2
    N budget hbudget hdimension f normalized Ψ hf (fun i site u _ => hΨ i site u)
    hnormalized z hpositive herr
  exact ⟨i.1.1, i.1.2, i.2.1 ∅, i.2.2.1, i.2.2.2 ∅, V, hV⟩

end Erdos3.VectorPolynomial

end

end OAI
