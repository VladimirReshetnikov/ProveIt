import OAI.Combinatorics.Progressions.Dynamics.AllocatedSlicedFactorBudget
import OAI.Combinatorics.Progressions.Dynamics.NormalizedNativeUniformBudget
import OAI.Combinatorics.Progressions.Dynamics.PreparedModularGeneralNativeBudget
import OAI.Combinatorics.Progressions.Estimates.CanonicalSlicedSourcePositivity
import OAI.Combinatorics.Progressions.Geometry.AllocatedAmbientBoxTests
import OAI.Combinatorics.Progressions.Geometry.SpatialSiteNativePartner

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
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

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

variable {T : Type*} [Fintype T] (a : T → ℂ)
variable (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)
local notation "LongSpace" => ((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle))
local notation "GridSpace" => ((Σ j, J j) → UnitAddCircle)

variable {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

theorem AllocatedModelPhysicalExpansionIdentity.common_cover
    (g : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) →
      T → (∀ a, (e a).Term) → Finset (Fin dim) → LongSpace × GridSpace → ℂ)
    (hidentity : AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm g)
    {L : ℝ≥0} (hg : ∀ label i k site, LipschitzWith L (g label i k site))
    (hgb : ∀ label i k site z, ‖g label i k site z‖ ≤ 1)
    {Nt V Cc Hs : {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {Lg : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a))
    (Vmax : ℝ≥0) (hVmax : ∀ a, V a ≤ Vmax) :
    ∃ gc : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) →
      T → (∀ a, (e a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ label i k site, LipschitzWith (L * (period * Vmax ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a}))
        (gc label i k site)) ∧
      (∀ label i k site z, ‖gc label i k site z‖ ≤ 1) ∧
      ∀ (v : X → (Unit ⊕ Fin dim) → ℤ),
        allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f
          (BooleanCubeKernel.physicalCubeRowSample U d rows p hm v) *
          allocatedFullGridChartModel B U b S rowSets d hb o bW e
            (BooleanCubeKernel.physicalCubeRowSample U d rows p hm v) =
          ∑ label, ∑ i, ∑ k, (((2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
            allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) * coverSiteCoefficient e k) *
            ∏ site, gc label i k site (physicalGridFactorInput (period * commonSitePeriod e k) p
              (fun z => (BooleanCubeKernel.physicalCubeVertexValue v site z : ℝ))) := by
  let gc := fun label i k site => g label i k site ∘ physicalFactorCoverMap period (commonSitePeriod e k)
  have hpos (k : ∀ a, (e a).Term) : NeZero (commonSitePeriod e k) := ⟨(commonSitePeriod_pos e he k).ne'⟩
  refine ⟨gc, ?_, fun label i k site z => hgb _ _ _ _ _, ?_⟩
  · intro label i k site
    let := hpos k
    have hk : (commonSitePeriod e k : ℝ≥0) ≤ Vmax ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} := by
      exact_mod_cast commonSitePeriod_le_pow e he hVmax k
    apply ((hg label i k site).comp (physicalFactorCoverMap_lipschitz_mul period (commonSitePeriod e k))).weaken
    simp only [Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hk zero_le) zero_le
  · intro v
    have hv (label) (i) (k : ∀ a, (e a).Term) (site) :
        gc label i k site (physicalGridFactorInput (period * commonSitePeriod e k) p
          (fun z => (BooleanCubeKernel.physicalCubeVertexValue v site z : ℝ))) =
        g label i k site (physicalMaskedFactorInput period p
          (fun z => (BooleanCubeKernel.physicalCubeVertexValue v site z : ℝ)),
          physicalGridFactorInput (commonSitePeriod e k) p
            (fun z => (BooleanCubeKernel.physicalCubeVertexValue v site z : ℝ))) := by
      let := hpos k
      exact congrArg (g label i k site) (physicalFactorCoverMap_input period (commonSitePeriod e k) p _)
    simp_rw [hv]
    exact hidentity v

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
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

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

variable {T : Type*} [Fintype T] (a : T → ℂ)
variable (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)
local notation "LongSpace" => ((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle))
local notation "GridSpace" => ((Σ j, J j) → UnitAddCircle)

variable {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

theorem AllocatedModelPhysicalExpansionIdentity.exists_large_source_term
    (g : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) →
      T → (∀ a, (e a).Term) → Finset (Fin dim) → LongSpace × GridSpace → ℂ)
    (hidentity : AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm g)
    {Ω : Type*} [Fintype Ω] (weight : Ω → ℂ)
    (frame : Ω → X → (Unit ⊕ Fin dim) → ℤ) {δ Cmass : ℝ}
    (hδ : 0 < δ) (hCmass : 0 < Cmass)
    (hmass : (∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ i, ∑ k,
      ‖((2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) *
        coverSiteCoefficient e k‖) ≤ Cmass)
    (hpositive : δ ≤ (∑ z, weight z *
      (allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f
        (BooleanCubeKernel.physicalCubeRowSample U d rows p hm (frame z)) *
      allocatedFullGridChartModel B U b S rowSets d hb o bW e
        (BooleanCubeKernel.physicalCubeRowSample U d rows p hm (frame z)))).re) :
    ∃ label i k, δ / Cmass ≤ ‖∑ z, weight z *
      ∏ site, g label i k site
        (physicalMaskedFactorInput period p
          (fun u => (BooleanCubeKernel.physicalCubeVertexValue (frame z) site u : ℝ)),
        physicalGridFactorInput (commonSitePeriod e k) p
          (fun u => (BooleanCubeKernel.physicalCubeVertexValue (frame z) site u : ℝ)))‖ := by
  let coeff := fun (label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) (i : T) (k : ∀ a, (e a).Term) => ((2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
    allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) *
    coverSiteCoefficient e k
  let value := fun label i k z => ∏ site, g label i k site
    (physicalMaskedFactorInput period p
      (fun u => (BooleanCubeKernel.physicalCubeVertexValue (frame z) site u : ℝ)),
    physicalGridFactorInput (commonSitePeriod e k) p
      (fun u => (BooleanCubeKernel.physicalCubeVertexValue (frame z) site u : ℝ)))
  have heq : (∑ z, weight z * ∑ label, ∑ i, ∑ k, coeff label i k * value label i k z) =
      ∑ label, ∑ i, ∑ k, coeff label i k * ∑ z, weight z * value label i k z := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro label _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro z _
    ring
  unfold AllocatedModelPhysicalExpansionIdentity at hidentity
  simp_rw [hidentity] at hpositive
  change δ ≤ (∑ z, weight z * ∑ label, ∑ i, ∑ k, coeff label i k * value label i k z).re at hpositive
  rw [heq] at hpositive
  obtain ⟨⟨label, i, k⟩, hterm⟩ := exists_large_weighted_term
    (fun v : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) ×
      T × (∀ a, (e a).Term) => coeff v.1 v.2.1 v.2.2)
    (fun v => ∑ z, weight z * value v.1 v.2.1 v.2.2 z) hδ hCmass
    (by simpa only [Fintype.sum_prod_type] using hmass)
    (by simpa only [Fintype.sum_prod_type] using hpositive.trans (Complex.re_le_norm _))
  exact ⟨label, i, k, hterm⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
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

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

variable {T : Type*} [Fintype T] (a : T → ℂ)
variable (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)
local notation "LongSpace" => ((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle))
local notation "GridSpace" => ((Σ j, J j) → UnitAddCircle)

variable {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

theorem AllocatedModelPhysicalExpansionIdentity.exists_common_cover_source
    (g : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) →
      T → (∀ a, (e a).Term) → Finset (Fin dim) → LongSpace × GridSpace → ℂ)
    (hidentity : AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm g)
    {L : ℝ≥0} (hg : ∀ label i k site, LipschitzWith L (g label i k site))
    (hgb : ∀ label i k site z, ‖g label i k site z‖ ≤ 1)
    {Nt V Cc Hs : {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {Lg : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a))
    (Vmax : ℝ≥0) (hVmax : ∀ a, V a ≤ Vmax)
    {Ω : Type*} [Fintype Ω] (weight : Ω → ℂ)
    (frame : Ω → X → (Unit ⊕ Fin dim) → ℤ) {δ Cmass : ℝ}
    (hδ : 0 < δ) (hCmass : 0 < Cmass)
    (hmass : (∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ i, ∑ k,
      ‖((2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) *
        coverSiteCoefficient e k‖) ≤ Cmass)
    (hpositive : δ ≤ (∑ z, weight z *
      (allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f
        (BooleanCubeKernel.physicalCubeRowSample U d rows p hm (frame z)) *
      allocatedFullGridChartModel B U b S rowSets d hb o bW e
        (BooleanCubeKernel.physicalCubeRowSample U d rows p hm (frame z)))).re) :
    ∃ cover : ℕ, 0 < cover ∧
      (cover : ℝ) ≤ period * (Vmax : ℝ) ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} ∧
    ∃ F : Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ site, LipschitzWith (L * (period * Vmax ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a})) (F site)) ∧
      (∀ site z, ‖F site z‖ ≤ 1) ∧
      δ / Cmass ≤ ‖∑ z, weight z * ∏ site, F site (physicalGridFactorInput cover p
        (fun u => (BooleanCubeKernel.physicalCubeVertexValue (frame z) site u : ℝ)))‖ := by
  obtain ⟨label, i, k, hterm⟩ := AllocatedModelPhysicalExpansionIdentity.exists_large_source_term
    B U b S x y₀ q d period r hr hb o bW e a f p hm g hidentity weight frame hδ hCmass hmass hpositive
  let cover := period * commonSitePeriod e k
  have hpos := commonSitePeriod_pos e he k
  let : NeZero (commonSitePeriod e k) := ⟨hpos.ne'⟩
  have hk : (commonSitePeriod e k : ℝ≥0) ≤
      Vmax ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} := by
    exact_mod_cast commonSitePeriod_le_pow e he hVmax k
  let F := fun site => g label i k site ∘ physicalFactorCoverMap period (commonSitePeriod e k)
  refine ⟨cover, Nat.mul_pos (NeZero.pos period) hpos, ?_, F, ?_, ?_, ?_⟩
  · have hkreal : (commonSitePeriod e k : ℝ) ≤
        (Vmax : ℝ) ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} := by exact_mod_cast hk
    dsimp only [cover]
    rw [Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left hkreal (Nat.cast_nonneg _)
  · intro site
    apply ((hg label i k site).comp (physicalFactorCoverMap_lipschitz_mul period (commonSitePeriod e k))).weaken
    simp only [Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hk zero_le) zero_le
  · intro site z
    exact hgb label i k site _
  · have hvalue (z : Ω) (site : Finset (Fin dim)) :
        F site (physicalGridFactorInput cover p
          (fun u => (BooleanCubeKernel.physicalCubeVertexValue (frame z) site u : ℝ))) =
        g label i k site (physicalMaskedFactorInput period p
          (fun u => (BooleanCubeKernel.physicalCubeVertexValue (frame z) site u : ℝ)),
          physicalGridFactorInput (commonSitePeriod e k) p
          (fun u => (BooleanCubeKernel.physicalCubeVertexValue (frame z) site u : ℝ))) :=
      congrArg (g label i k site) (physicalFactorCoverMap_input period (commonSitePeriod e k) p _)
    simpa only [hvalue] using hterm

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
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

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

variable {T : Type*} [Fintype T] (a : T → ℂ)
variable (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)
local notation "LongSpace" => ((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle))
local notation "GridSpace" => ((Σ j, J j) → UnitAddCircle)

variable {X : Type*} [Fintype X] (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

variable (spatialModulus : ℕ) [NeZero spatialModulus] (stride N : X → ℕ)
local notation "refined" => residueRefinedPeriod spatialModulus stride
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod spatialModulus stride)) → PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
  (allocatedPrincipalSides B U b S))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod spatialModulus stride)) {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable {W τ ξ mesh : ℝ} (hW : 0 ≤ W) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N stride) 4
local notation "widths" => narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
local notation "reconstruct" => allocatedWholeResidueReconstruction B U b S X spatialModulus stride wholeReference x base label
local notation "volume" => ∏ z, ∏ i, physicalSpatialOutputScale (Fin dim)
  (trimmedSpatialRootScale τ N stride z) (trimmedSpatialSlopeScale W τ N stride z) S.value i
local notation "terms" => (X → SpatialSiteLabel (Fin dim) spatialModulus 4 mesh)
local notation "twist" => allocatedRecenteredSpatialTwist (τ := τ) B U b S X spatialModulus stride wholeReference x N mesh base label

noncomputable def allocatedRecenteredFiniteModelSource
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) : ℂ :=
  ∑ z : cells × window, (selectedResidueCellWeight stride cells widths z.1 : ℂ) *
    allocatedRecenteredResidueWeight (τ := τ) B U b S X spatialModulus stride wholeReference x hM selection hx
      N hW mesh base cells (physicalCubeSiteTest test) label z.1 z.2.val *
    (allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f
      (physicalCubeRowSample U d rows p hm (reconstruct z.1.val z.2.val)) *
    allocatedFullGridChartModel B U b S rowSets d hb o bW e
      (physicalCubeRowSample U d rows p hm (reconstruct z.1.val z.2.val)))

theorem AllocatedModelPhysicalExpansionIdentity.exists_twisted_common_cover_source
    (g : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) →
      T → (∀ a, (e a).Term) → Finset (Fin dim) → LongSpace × GridSpace → ℂ)
    (hidentity : AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm g)
    {L : ℝ≥0} (hg : ∀ label i k site, LipschitzWith L (g label i k site))
    (hgb : ∀ label i k site z, ‖g label i k site z‖ ≤ 1)
    {Nt V Cc Hs : {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {Lg : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a))
    (Vmax : ℝ≥0) (hVmax : ∀ a, V a ≤ Vmax)
    (hstride : ∀ z, 0 < stride z) (hmesh : 0 < mesh)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (spatialModulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection))
    (hV : ∀ z, 0 < widths z) (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z)
    (test : Finset (Fin dim) → (X → ℝ) → ℂ)
    {δ Cmodel Cspatial : ℝ} (hδ : 0 < δ) (hCmodel : 0 < Cmodel) (hCspatial : 0 < Cspatial)
    (hmass : (∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ i, ∑ k,
      ‖((2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) *
        coverSiteCoefficient e k‖) ≤ Cmodel)
    (hspatial : allocatedSpatialCoefficientCap X selection M spatialModulus mesh ≤ Cspatial)
    (hpositive : δ ≤ (allocatedRecenteredFiniteModelSource (τ := τ) (ξ := ξ) (mesh := mesh)
      B U b S x y₀ q d period r hr hb o bW e a f p hm spatialModulus stride N wholeReference label
      hM selection hx hW base cells test).re) :
    ∃ cover : ℕ, 0 < cover ∧
      (cover : ℝ) ≤ period * (Vmax : ℝ) ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} ∧
    ∃ F : Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ site, LipschitzWith (L * (period * Vmax ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a})) (F site)) ∧
      (∀ site z, ‖F site z‖ ≤ 1) ∧
    ∃ (cell : cells) (t : terms),
      allocatedSpatialExpansionCoefficient B U b S x X hM selection hx spatialModulus hW mesh
        (principalResidueLabel spatialModulus (wholeReference label)) t ≠ 0 ∧
      (∀ site u, ‖twist cell.val t site u‖ ≤ 1) ∧
      δ / (Cmodel * Cspatial) ≤ ‖(∑ v ∈ window,
        (∏ site, test site (fun u => (physicalCubeVertexValue (reconstruct cell.val v) site u : ℝ)) *
          twist cell.val t site (physicalCubeVertexValue (reconstruct cell.val v) site)) *
        ∏ site, F site (physicalGridFactorInput cover p
          (fun u => (physicalCubeVertexValue (reconstruct cell.val v) site u : ℝ)))) / ((volume : ℝ) : ℂ)‖ := by
  let weight : cells × window → ℂ := fun z => (selectedResidueCellWeight stride cells widths z.1 : ℂ) *
    allocatedRecenteredResidueWeight (τ := τ) B U b S X spatialModulus stride wholeReference x hM selection hx
      N hW mesh base cells (physicalCubeSiteTest test) label z.1 z.2.val
  let frame : cells × window → X → (Unit ⊕ Fin dim) → ℤ := fun z => reconstruct z.1.val z.2.val
  obtain ⟨cover, hcover, hcoverBound, F, hF, hFb, hsource⟩ :=
    AllocatedModelPhysicalExpansionIdentity.exists_common_cover_source B U b S x y₀ q d period r hr hb o bW e a f p hm
      g hidentity hg hgb he Vmax hVmax weight frame hδ hCmodel hmass hpositive
  let value : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ := fun v => ∏ site, F site (physicalGridFactorInput cover p
    (fun u => (physicalCubeVertexValue v site u : ℝ)))
  have hsource' : δ / Cmodel ≤ ‖∑ acell : cells, (selectedResidueCellWeight stride cells widths acell : ℂ) *
      ∑ v ∈ window, allocatedRecenteredResidueWeight (τ := τ) B U b S X spatialModulus stride wholeReference x
        hM selection hx N hW mesh base cells (physicalCubeSiteTest test) label acell v * value (reconstruct acell.val v)‖ := by
    convert hsource using 1
    congr 1
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro acell _
    rw [Finset.mul_sum, ← Finset.sum_coe_sort window]
    apply Finset.sum_congr rfl
    intro v _
    dsimp only [weight, frame, value]
    ring
  obtain ⟨cell, t, hct, ht, hterm⟩ := allocatedRecentered_exists_twisted_source (ξ := ξ) B U b S X spatialModulus stride
    wholeReference x N mesh base hM selection hx hW cells hstride hmesh hbudget hperiod hV hZ
    label test value (div_pos hδ hCmodel) hCspatial hspatial hsource'
  refine ⟨cover, hcover, hcoverBound, F, hF, hFb, cell, t, hct, ht, ?_⟩
  simpa only [div_div, value] using hterm

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem exists_allocatedRecenteredFactor_normalization (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
      {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
      (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
      {J : Fin m → Type*} [∀ j, Fintype (J j)]
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
      {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
      {X Y : Type*} [Fintype X] [PseudoMetricSpace Y]
      (selection : Fin dim ↪ G) {M modulus : ℕ} [NeZero modulus]
      {p E analytic : ℝ}, 0 ≤ p → 0 ≤ E → 0 ≤ analytic →
      (Fintype.card G : ℝ) ≤ p → (Fintype.card X : ℝ) ≤ p → ((dim + 1 : ℕ) : ℝ) ≤ p →
      0 < M → (M : ℝ) ≤ Real.exp p → modulus ≤ M ^ (m + 1) →
      ∀ (r : ℝ≥0), (r : ℝ) = allocatedEarlyRecenteredMesh X selection M modulus p E →
      ∀ (stride N : X → ℕ) {τ : ℝ},
      (∀ i, 0 < N i) → (∀ i, 0 < stride i) → (∀ i, (stride i : ℝ) ≤ Real.exp p) →
      0 < τ → 1 / τ ≤ Real.exp p →
      ∀ (wholeReference :
        (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus stride)) →
          PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
        (x : G → IntegerScalarCubeBox (Fin dim) S.value) (base : X → ℤ)
        (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus stride))
        (cell : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)
        (t : X → SpatialSiteLabel (Fin dim) modulus 4 r) (site : Finset (Fin dim))
        (F : Y → ℂ) {L : ℝ≥0}, LipschitzWith L F → (∀ y, ‖F y‖ ≤ 1) → (L : ℝ) ≤ Real.exp analytic →
      0 < residueRefinedPeriod modulus stride ∧
      (residueRefinedPeriod modulus stride : ℝ) ≤ Real.exp (((m + 1 : ℕ) : ℝ) * p + Fintype.card X * p) ∧
      ∃ (mask : (X → ZMod (residueRefinedPeriod modulus stride)) → ℂ)
        (H : (X → ℝ) × Y → ℂ),
        (∀ z, ‖mask z‖ ≤ 1) ∧ (∀ v, ‖H v‖ ≤ 1) ∧
        LipschitzWith ⟨Real.exp ((p + E + analytic + A) ^ A), Real.exp_nonneg _⟩ H ∧
        ∀ (u : X → ℤ) (y : Y),
          allocatedRecenteredSpatialTwist (τ := τ) B U b S X modulus stride wholeReference x N r base label cell t site u * F y =
            mask (fun i => (u i : ZMod (residueRefinedPeriod modulus stride))) * H (fun i => (u i : ℝ) / N i, y) := by
  obtain ⟨A, hA, hfactor⟩ := exists_allocatedSlicedFactor_budget m dim
  refine ⟨A, hA, ?_⟩
  intro G _ _ I _ n B _ J _ U b R σ S X Y _ _ selection M modulus _ p E analytic hp hE ha hG hX hdim
    hM hMP hmodulus r hr stride N τ hN hs hsP hτ hτP wholeReference x base label cell t site F L hF hFb hL
  let root := allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (wholeReference label)
  let dirs := allocatedPhysicalCubeDirections B U b S x (wholeReference label)
  let residue := boundedColumnResidueRepresentative stride cell
  let hdiv := stride_mul_dvd_residueRefinedPeriod modulus stride
  let mask := physicalResidueSpatialMaskMod root dirs base residue stride 4 r hdiv t site
  let H := physicalSpatialAnalyticContinuous (τ := τ) root dirs base residue stride N r t site F
  have hmod : (modulus : ℝ) ≤ Real.exp (((m + 1 : ℕ) : ℝ) * p) := by
    calc
      _ ≤ (M : ℝ) ^ (m + 1) := by exact_mod_cast hmodulus
      _ ≤ (Real.exp p) ^ (m + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hMP _
      _ = _ := (Real.exp_nat_mul _ _).symm
  obtain ⟨hHb, hHL⟩ := hfactor selection hp hE ha hG hX hdim hM hMP hmodulus r hr root dirs base residue stride N
    hN hs hτ hτP t site F hF hFb hL
  refine ⟨residueRefinedPeriod_pos (Nat.pos_of_ne_zero (NeZero.ne modulus)) stride hs,
    residueRefinedPeriod_exp_bound modulus stride hmod hsP, mask, H,
    physicalResidueSpatialMaskMod_norm root dirs base residue stride 4 r hdiv t site, hHb, hHL, ?_⟩
  intro u y
  exact physicalSpatialAnalytic_normalized root dirs base residue stride N r t site F hN hdiv u y

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {s nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin (s + 1)) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin (s + 1))))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U b S))
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

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin (s + 1))))

variable {T : Type*} [Fintype T] (a : T → ℂ)
variable (f : T → Finset (Fin (s + 1)) → (LayerSamplerAxis I n → ℝ) → ℂ)
local notation "LongSpace" => ((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle))
local notation "GridSpace" => ((Σ j, J j) → UnitAddCircle)

variable (p : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

variable (spatialModulus : ℕ) [NeZero spatialModulus] (stride N : (Fin nX) → ℕ)
local notation "refined" => residueRefinedPeriod spatialModulus stride
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod refined)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod spatialModulus stride)) → PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1))
  (allocatedPrincipalSides B U b S))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod spatialModulus stride)) {M : ℕ} (hM : 0 < M) (selection : Fin (s + 1) ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable {W τ ξ mesh : ℝ} (hW : 0 ≤ W) (base : (Fin nX) → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
local notation "window" => spatialWindow (α := Fin (s + 1)) (trimmedSpatialRootScale τ N stride) 4
local notation "widths" => narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
local notation "reconstruct" => allocatedWholeResidueReconstruction B U b S (Fin nX) spatialModulus stride wholeReference x base label
local notation "volume" => ∏ z, ∏ i, physicalSpatialOutputScale (Fin (s + 1))
  (trimmedSpatialRootScale τ N stride z) (trimmedSpatialSlopeScale W τ N stride z) S.value i
local notation "terms" => ((Fin nX) → SpatialSiteLabel (Fin (s + 1)) spatialModulus 4 mesh)
local notation "twist" => allocatedRecenteredSpatialTwist (τ := τ) B U b S (Fin nX) spatialModulus stride wholeReference x N mesh base label

variable [∀ i, NeZero (N i)]
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (wholeReference label)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (wholeReference label)
local notation "windowMask" => (fun acell : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride =>
  physicalResidueWindowSiteMask root dirs base
    (boundedColumnResidueRepresentative stride acell) stride (trimmedSpatialRootScale τ N stride) 4)
attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem AllocatedModelPhysicalExpansionIdentity.exists_native_source
    (g : (Finset (Fin (s + 1)) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) →
      T → (∀ a, (e a).Term) → Finset (Fin (s + 1)) → LongSpace × GridSpace → ℂ)
    (hidentity : AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm g)
    {L : ℝ≥0} (hg : ∀ label i k site, LipschitzWith L (g label i k site))
    (hgb : ∀ label i k site z, ‖g label i k site z‖ ≤ 1)
    {Nt V Cc Hs : {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {Lg : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a))
    (Vmax : ℝ≥0) (hVmax : ∀ a, V a ≤ Vmax)
    (hstride : ∀ z, 0 < stride z) (hmesh : 0 < mesh) (hmargin : 3 + 2 * mesh ≤ 4)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hperiod : integerScalarLattice (Unit ⊕ Fin (s + 1)) (spatialModulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection))
    (hV : ∀ z, 0 < widths z) (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z)
    (signal : ((Fin nX) → ℤ) → ℂ)
    (hsignal : ∀ u ∈ integerBox N, ‖signal u‖ ≤ 1)
    (hzero : ∀ u, u ∉ integerBox N → signal u = 0)
    (hτ : 0 < τ)
    {Psource Pvolume : ℝ} (hPsource : 0 ≤ Psource) (hPvolume : 0 ≤ Pvolume)
    (hdim : (nX : ℝ) ≤ Psource + Pvolume)
    (hvolumeRatio : (integerBoxCubeCount N (s + 1) : ℝ) / volume ≤ Real.exp Pvolume)
    {δ Cmodel Cspatial : ℝ} (hδ : 0 < δ) (hCmodel : 0 < Cmodel) (hCspatial : 0 < Cspatial)
    (hmass : (∑ label : Finset (Fin (s + 1)) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ i, ∑ k,
      ‖((2 : ℂ) ^ Fintype.card (Finset (Fin (s + 1))) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) *
        coverSiteCoefficient e k‖) ≤ Cmodel)
    (hspatial : allocatedSpatialCoefficientCap (Fin nX) selection M spatialModulus mesh ≤ Cspatial)
    (hpositive : δ ≤ (allocatedRecenteredFiniteModelSource (τ := τ) (ξ := ξ) (mesh := mesh)
      B U b S x y₀ q d period r hr hb o bW e a f p hm spatialModulus stride N wholeReference label
      hM selection hx hW base cells (integerSelfSiteTest (s + 1) signal)).re)
    (hgain : Real.exp (-Psource) ≤ δ / (Cmodel * Cspatial)) :
    ∃ cover : ℕ, 0 < cover ∧
      (cover : ℝ) ≤ period * (Vmax : ℝ) ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} ∧
    ∃ F : Finset (Fin (s + 1)) → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ site, LipschitzWith (L * (period * Vmax ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a})) (F site)) ∧
      (∀ site z, ‖F site z‖ ≤ 1) ∧
    ∃ (cell : cells) (t : terms),
      let ψ := fun u : (Fin nX) → ℤ =>
        twist cell.val t ∅ u * F ∅ (physicalGridFactorInput cover p (fun i => (u i : ℝ)))
      (∀ u, ‖ψ u‖ ≤ 1) ∧
      ∃ V : NativeSampleCorrelation (fun _ : (Fin nX) => 1) s
        ((Psource + Pvolume + 2) ^ Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s))
        (integerBox N) id (fun u => signal u * ψ u),
        V.test.normBound ≤ 1 ∧
        Real.exp (-((Psource + Pvolume + 2) ^ Classical.choose
          (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s))) ≤
          ‖𝔼 u ∈ integerBox N, signal u * star (star (ψ u) * V.test.eval u)‖ := by
  obtain ⟨cover, hcover, hcoverBound, F, hF, hFb, cell, t, hct, ht, hsource⟩ :=
    hidentity.exists_twisted_common_cover_source B U b S x y₀ q d period r hr hb o bW e a f p hm
      spatialModulus stride N wholeReference label hM selection hx hW base cells g hg hgb he Vmax hVmax
      hstride hmesh hbudget hperiod hV hZ (integerSelfSiteTest (s + 1) signal)
      hδ hCmodel hCspatial hmass hspatial hpositive
  let analytic := fun site (u : (Fin nX) → ℤ) => F site (physicalGridFactorInput cover p (fun i => (u i : ℝ)))
  have hvol : 0 < volume := by
    apply Finset.prod_pos
    intro i _
    apply Finset.prod_pos
    intro j _
    have hsc := trimmedSpatial_scales_pos hW hτ N stride i (NeZero.pos (N i)) (hstride i)
    exact physicalSpatialOutputScale_pos (Fin (s + 1)) hsc.1 hsc.2 (Nat.cast_pos.mpr S.positive) j
  have hwindow (v) (hv : v ∉ window) :
      (∏ site, physicalResidueSpatialSiteFactor root dirs base
        (boundedColumnResidueRepresentative stride cell.val) stride 4 mesh
        (trimmedSpatialRootScale τ N stride) t site
        (physicalCubeVertexValue (physicalResidueReconstruction root dirs base
          (boundedColumnResidueRepresentative stride cell.val) stride v) site)) = 0 := by
    rw [physicalResidueSpatialSiteFactor_prod root dirs base
      (boundedColumnResidueRepresentative stride cell.val) stride hstride]
    exact allocatedSpatialExpansionCoefficient_term_zero_outside B U b S x (Fin nX) hM selection hx
      spatialModulus (trimmedSpatialRootScale τ N stride) hW mesh hbudget
      (fun i => (trimmedSpatial_scales_pos hW hτ N stride i (NeZero.pos (N i)) (hstride i)).1)
      hmesh hmargin (principalResidueLabel spatialModulus (wholeReference label)) t hct v hv
  have hnative := native_partner_of_supported_spatial_site_source root dirs base
    (boundedColumnResidueRepresentative stride cell.val) stride N (trimmedSpatialRootScale τ N stride) 4 mesh t
    signal analytic hstride hmesh hsignal hzero (fun site u _ => hFb site _) hwindow hPsource hPvolume hdim hvol hvolumeRatio
  have hsource' := hgain.trans hsource
  simp only [integerSelfSiteTest, Int.floor_intCast, ← Finset.prod_mul_distrib, mul_assoc] at hsource'
  obtain ⟨V, hnorm, hcorr⟩ := hnative hsource'
  refine ⟨cover, hcover, hcoverBound, F, hF, hFb, cell, t, ?_, V, hnorm, hcorr⟩
  intro u
  rw [norm_mul]
  exact (mul_le_mul (ht ∅ u) (hFb ∅ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {s nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin (s + 1)) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin (s + 1))))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U b S))
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

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin (s + 1))))

variable {T : Type*} [Fintype T] (a : T → ℂ)
variable (f : T → Finset (Fin (s + 1)) → (LayerSamplerAxis I n → ℝ) → ℂ)
local notation "LongSpace" => ((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle))
local notation "GridSpace" => ((Σ j, J j) → UnitAddCircle)

variable (p : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

variable (spatialModulus : ℕ) [NeZero spatialModulus] (stride N : (Fin nX) → ℕ)
local notation "refined" => residueRefinedPeriod spatialModulus stride
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod refined)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod spatialModulus stride)) → PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1))
  (allocatedPrincipalSides B U b S))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod spatialModulus stride)) {M : ℕ} (hM : 0 < M) (selection : Fin (s + 1) ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable {W τ ξ mesh : ℝ} (hW : 0 ≤ W) (base : (Fin nX) → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
local notation "window" => spatialWindow (α := Fin (s + 1)) (trimmedSpatialRootScale τ N stride) 4
local notation "widths" => narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
local notation "reconstruct" => allocatedWholeResidueReconstruction B U b S (Fin nX) spatialModulus stride wholeReference x base label
local notation "volume" => ∏ z, ∏ i, physicalSpatialOutputScale (Fin (s + 1))
  (trimmedSpatialRootScale τ N stride z) (trimmedSpatialSlopeScale W τ N stride z) S.value i
local notation "terms" => ((Fin nX) → SpatialSiteLabel (Fin (s + 1)) spatialModulus 4 mesh)
local notation "twist" => allocatedRecenteredSpatialTwist (τ := τ) B U b S (Fin nX) spatialModulus stride wholeReference x N mesh base label

variable [∀ i, NeZero (N i)]
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (wholeReference label)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (wholeReference label)
local notation "windowMask" => (fun acell : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride =>
  physicalResidueWindowSiteMask root dirs base
    (boundedColumnResidueRepresentative stride acell) stride (trimmedSpatialRootScale τ N stride) 4)
attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem AllocatedModelPhysicalExpansionIdentity.exists_native_source_of_transfer
    (g : (Finset (Fin (s + 1)) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) →
      T → (∀ a, (e a).Term) → Finset (Fin (s + 1)) → LongSpace × GridSpace → ℂ)
    (hidentity : AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm g)
    {L : ℝ≥0} (hg : ∀ label i k site, LipschitzWith L (g label i k site))
    (hgb : ∀ label i k site z, ‖g label i k site z‖ ≤ 1)
    {Nt V Cc Hs : {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {Lg : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a))
    (Vmax : ℝ≥0) (hVmax : ∀ a, V a ≤ Vmax)
    (hstride : ∀ z, 0 < stride z) (hmesh : 0 < mesh) (hmargin : 3 + 2 * mesh ≤ 4)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hperiod : integerScalarLattice (Unit ⊕ Fin (s + 1)) (spatialModulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection))
    (hV : ∀ z, 0 < widths z) (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z)
    (signal : ((Fin nX) → ℤ) → ℂ)
    (hsignal : ∀ u ∈ integerBox N, ‖signal u‖ ≤ 1)
    (hzero : ∀ u, u ∉ integerBox N → signal u = 0)
    (hτ : 0 < τ)
    {pGain Emodel Espatial Eerror Znormalizer Pvolume : ℝ}
    (hpGain : 0 ≤ pGain) (hEmodel : 0 ≤ Emodel) (hEspatial : 0 ≤ Espatial)
    (hEerror : pGain + 32 ≤ Eerror) (hZnormalizer : 1 / 2 ≤ Znormalizer)
    (hPvolume : 0 ≤ Pvolume)
    (hdim : (nX : ℝ) ≤ pGain + 8 + Emodel + Espatial + Pvolume)
    (hvolumeRatio : (integerBoxCubeCount N (s + 1) : ℝ) / volume ≤ Real.exp Pvolume)
    (hmass : (∑ label : Finset (Fin (s + 1)) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ i, ∑ k,
      ‖((2 : ℂ) ^ Fintype.card (Finset (Fin (s + 1))) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) *
        coverSiteCoefficient e k‖) ≤ Real.exp Emodel)
    (hspatial : allocatedSpatialCoefficientCap (Fin nX) selection M spatialModulus mesh ≤ Real.exp Espatial)
    (hpositive : Znormalizer * (Real.exp (-pGain) / 2 - Real.exp (-Eerror) - Real.exp (-Eerror)) -
      Real.exp (-Eerror) - Real.exp (-Eerror) ≤ (allocatedRecenteredFiniteModelSource (τ := τ) (ξ := ξ) (mesh := mesh)
      B U b S x y₀ q d period r hr hb o bW e a f p hm spatialModulus stride N wholeReference label
      hM selection hx hW base cells (integerSelfSiteTest (s + 1) signal)).re)
    :
    let Psource := pGain + 8 + Emodel + Espatial
    ∃ cover : ℕ, 0 < cover ∧
      (cover : ℝ) ≤ period * (Vmax : ℝ) ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} ∧
    ∃ F : Finset (Fin (s + 1)) → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ site, LipschitzWith (L * (period * Vmax ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a})) (F site)) ∧
      (∀ site z, ‖F site z‖ ≤ 1) ∧
    ∃ (cell : cells) (t : terms),
      let ψ := fun u : (Fin nX) → ℤ =>
        twist cell.val t ∅ u * F ∅ (physicalGridFactorInput cover p (fun i => (u i : ℝ)))
      (∀ u, ‖ψ u‖ ≤ 1) ∧
      ∃ V : NativeSampleCorrelation (fun _ : (Fin nX) => 1) s
        ((Psource + Pvolume + 2) ^ Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s))
        (integerBox N) id (fun u => signal u * ψ u),
        V.test.normBound ≤ 1 ∧
        Real.exp (-((Psource + Pvolume + 2) ^ Classical.choose
          (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s))) ≤
          ‖𝔼 u ∈ integerBox N, signal u * star (star (ψ u) * V.test.eval u)‖ := by
  intro Psource
  have hsource := slicedSource_transfer_combined_exp hEerror hZnormalizer hpositive
  have hgain := slicedSource_selected_gain_exp (δ := Real.exp (-(pGain + 8)))
    (Cmodel := Real.exp Emodel) (Cspatial := Real.exp Espatial) le_rfl
    (Real.exp_pos _) (Real.exp_pos _) le_rfl le_rfl
  exact hidentity.exists_native_source B U b S x y₀ q d period r hr hb o bW e a f p hm
    spatialModulus stride N wholeReference label hM selection hx hW base cells g hg hgb he Vmax hVmax
    hstride hmesh hmargin hbudget hperiod hV hZ signal hsignal hzero hτ
    (show 0 ≤ Psource by dsimp [Psource]; positivity) hPvolume hdim hvolumeRatio
    (Real.exp_pos _) (Real.exp_pos _) (Real.exp_pos _) hmass hspatial hsource hgain

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uG uI uB uJ

open Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {s nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin (s + 1)) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin (s + 1))))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin (s + 1))))

variable {T : Type*} [Fintype T] (a : T → ℂ)
variable (f : T → Finset (Fin (s + 1)) → (LayerSamplerAxis I n → ℝ) → ℂ)
local notation "LongSpace" => ((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle))
local notation "GridSpace" => ((Σ j, J j) → UnitAddCircle)

variable (p : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

variable (spatialModulus : ℕ) [NeZero spatialModulus] (stride N : (Fin nX) → ℕ)
local notation "refined" => residueRefinedPeriod spatialModulus stride
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod refined)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod spatialModulus stride)) → PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1))
  (allocatedPrincipalSides B U b S))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod spatialModulus stride)) {M : ℕ} (hM : 0 < M) (selection : Fin (s + 1) ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable {W τ ξ mesh : ℝ} (hW : 0 ≤ W) (base : (Fin nX) → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
local notation "window" => spatialWindow (α := Fin (s + 1)) (trimmedSpatialRootScale τ N stride) 4
local notation "widths" => narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
local notation "reconstruct" => allocatedWholeResidueReconstruction B U b S (Fin nX) spatialModulus stride wholeReference x base label
local notation "volume" => ∏ z, ∏ i, physicalSpatialOutputScale (Fin (s + 1))
  (trimmedSpatialRootScale τ N stride z) (trimmedSpatialSlopeScale W τ N stride z) S.value i
local notation "terms" => ((Fin nX) → SpatialSiteLabel (Fin (s + 1)) spatialModulus 4 mesh)
local notation "twist" => allocatedRecenteredSpatialTwist (τ := τ) B U b S (Fin nX) spatialModulus stride wholeReference x N mesh base label

variable [∀ i, NeZero (N i)]
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (wholeReference label)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (wholeReference label)
local notation "windowMask" => (fun acell : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride =>
  physicalResidueWindowSiteMask root dirs base
    (boundedColumnResidueRepresentative stride acell) stride (trimmedSpatialRootScale τ N stride) 4)
attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem AllocatedModelPhysicalExpansionIdentity.exists_normalized_native_source_of_transfer
    (g : (Finset (Fin (s + 1)) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) →
      T → (∀ a, (e a).Term) → Finset (Fin (s + 1)) → LongSpace × GridSpace → ℂ)
    (hidentity : AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm g)
    {L : ℝ≥0} (hg : ∀ label i k site, LipschitzWith L (g label i k site))
    (hgb : ∀ label i k site z, ‖g label i k site z‖ ≤ 1)
    {Nt V Cc Hs : {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {Lg : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a))
    (Vmax : ℝ≥0) (hVmax : ∀ a, V a ≤ Vmax)
    (hstride : ∀ z, 0 < stride z) (hmesh : 0 < mesh) (hmargin : 3 + 2 * mesh ≤ 4)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hperiod : integerScalarLattice (Unit ⊕ Fin (s + 1)) (spatialModulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection))
    (hV : ∀ z, 0 < widths z) (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z)
    (signal : ((Fin nX) → ℤ) → ℂ)
    (hsignal : ∀ u ∈ integerBox N, ‖signal u‖ ≤ 1)
    (hzero : ∀ u, u ∉ integerBox N → signal u = 0)
    (hτ : 0 < τ)
    {pGain Emodel Espatial Eerror Znormalizer Pvolume : ℝ}
    (hpGain : 0 ≤ pGain) (hEmodel : 0 ≤ Emodel) (hEspatial : 0 ≤ Espatial)
    (hEerror : pGain + 32 ≤ Eerror) (hZnormalizer : 1 / 2 ≤ Znormalizer)
    (hPvolume : 0 ≤ Pvolume)
    (hdim : (nX : ℝ) ≤ pGain + 8 + Emodel + Espatial + Pvolume)
    (hvolumeRatio : (integerBoxCubeCount N (s + 1) : ℝ) / volume ≤ Real.exp Pvolume)
    (hmass : (∑ label : Finset (Fin (s + 1)) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ i, ∑ k,
      ‖((2 : ℂ) ^ Fintype.card (Finset (Fin (s + 1))) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) *
        coverSiteCoefficient e k‖) ≤ Real.exp Emodel)
    (hspatial : allocatedSpatialCoefficientCap (Fin nX) selection M spatialModulus mesh ≤ Real.exp Espatial)
    (hpositive : Znormalizer * (Real.exp (-pGain) / 2 - Real.exp (-Eerror) - Real.exp (-Eerror)) -
      Real.exp (-Eerror) - Real.exp (-Eerror) ≤ (allocatedRecenteredFiniteModelSource (τ := τ) (ξ := ξ) (mesh := mesh)
      B U b S x y₀ q d period r hr hb o bW e a f p hm spatialModulus stride N wholeReference label
      hM selection hx hW base cells (integerSelfSiteTest (s + 1) signal)).re)
    {pGeometry Ecoarse analytic : ℝ}
    (hpGeometry : 0 ≤ pGeometry) (hEcoarse : 0 ≤ Ecoarse) (hanalytic : 0 ≤ analytic)
    (hGGeometry : (Fintype.card G : ℝ) ≤ pGeometry)
    (hXGeometry : (nX : ℝ) ≤ pGeometry) (hdimGeometry : ((s + 2 : ℕ) : ℝ) ≤ pGeometry)
    (hMGeometry : (M : ℝ) ≤ Real.exp pGeometry) (hmodulusGeometry : spatialModulus ≤ M ^ (m + 1))
    (hmeshEarly : mesh = allocatedEarlyRecenteredMesh (Fin nX) selection M spatialModulus pGeometry Ecoarse)
    (hstrideGeometry : ∀ i, (stride i : ℝ) ≤ Real.exp pGeometry)
    (hτGeometry : 1 / τ ≤ Real.exp pGeometry)
    (hLanalytic : ((L * (period * Vmax ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a}) : ℝ≥0) : ℝ) ≤ Real.exp analytic) :
    let Psource := pGain + 8 + Emodel + Espatial
    let A := Classical.choose (exists_allocatedRecenteredFactor_normalization.{uG,uI,uB,uJ,0,uJ} m (s + 1))
    ∃ cover : ℕ, 0 < cover ∧
      (cover : ℝ) ≤ period * (Vmax : ℝ) ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} ∧
      0 < residueRefinedPeriod spatialModulus stride ∧
      (residueRefinedPeriod spatialModulus stride : ℝ) ≤
        Real.exp (((m + 1 : ℕ) : ℝ) * pGeometry + Fintype.card (Fin nX) * pGeometry) ∧
    ∃ (mask : ((Fin nX) → ZMod (residueRefinedPeriod spatialModulus stride)) → ℂ)
      (H : ((Fin nX) → ℝ) × ((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ z, ‖mask z‖ ≤ 1) ∧ (∀ v, ‖H v‖ ≤ 1) ∧
      LipschitzWith ⟨Real.exp ((pGeometry + Ecoarse + analytic + A) ^ A), Real.exp_nonneg _⟩ H ∧
      let ψ := fun u : (Fin nX) → ℤ =>
        mask (fun i => (u i : ZMod (residueRefinedPeriod spatialModulus stride))) *
          H (fun i => (u i : ℝ) / N i, physicalGridFactorInput cover p (fun i => (u i : ℝ)))
      (∀ u, ‖ψ u‖ ≤ 1) ∧
      ∃ V : NativeSampleCorrelation (fun _ : (Fin nX) => 1) s
        ((Psource + Pvolume + 2) ^ Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s))
        (integerBox N) id (fun u => signal u * ψ u),
        V.test.normBound ≤ 1 ∧
        Real.exp (-((Psource + Pvolume + 2) ^ Classical.choose
          (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s))) ≤
          ‖𝔼 u ∈ integerBox N, signal u * star (star (ψ u) * V.test.eval u)‖ := by
  intro Psource A
  obtain ⟨cover, hcover, hcoverBound, F, hF, hFb, cell, t, hψ, Vnative, hVnative, hcorrelation⟩ :=
    hidentity.exists_native_source_of_transfer B U b S x y₀ q d period r hr hb o bW e a f p hm
      spatialModulus stride N wholeReference label hM selection hx hW base cells g hg hgb he Vmax hVmax
      hstride hmesh hmargin hbudget hperiod hV hZ signal hsignal hzero hτ
      hpGain hEmodel hEspatial hEerror hZnormalizer hPvolume hdim hvolumeRatio hmass hspatial hpositive
  have hN (i) : 0 < N i := Nat.pos_of_ne_zero (NeZero.ne (N i))
  obtain ⟨hperiodPos, hperiodBound, mask, H, hmask, hH, hLip, hfactor⟩ :=
    (Classical.choose_spec (exists_allocatedRecenteredFactor_normalization.{uG,uI,uB,uJ,0,uJ} m (s + 1))).2
      B U b S selection hpGeometry hEcoarse hanalytic hGGeometry
      (by simpa only [Fintype.card_fin] using hXGeometry) hdimGeometry hM hMGeometry hmodulusGeometry
      ⟨mesh, hmesh.le⟩ hmeshEarly stride N hN hstride hstrideGeometry hτ hτGeometry
      wholeReference x base label cell.val t ∅ (F ∅) (hF ∅) (hFb ∅) hLanalytic
  refine ⟨cover, hcover, hcoverBound, hperiodPos, hperiodBound, mask, H, hmask, hH, hLip, ?_⟩
  have heq (u : (Fin nX) → ℤ) :
      twist cell.val t ∅ u * F ∅ (physicalGridFactorInput cover p (fun i => (u i : ℝ))) =
      mask (fun i => (u i : ZMod (residueRefinedPeriod spatialModulus stride))) *
        H (fun i => (u i : ℝ) / N i, physicalGridFactorInput cover p (fun i => (u i : ℝ))) :=
    hfactor u _
  constructor
  · simpa only [← heq] using hψ
  · refine ⟨{ Vnative with correlation := ?_ }, hVnative, ?_⟩
    · simpa only [heq] using Vnative.correlation
    · simpa only [heq] using hcorrelation

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uG uI uB uJ

open Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {s nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin (s + 1)) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin (s + 1))))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin (s + 1))))

variable {T : Type*} [Fintype T] (a : T → ℂ)
variable (f : T → Finset (Fin (s + 1)) → (LayerSamplerAxis I n → ℝ) → ℂ)
local notation "LongSpace" => ((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle))
local notation "GridSpace" => ((Σ j, J j) → UnitAddCircle)

variable (p : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

variable (spatialModulus : ℕ) [NeZero spatialModulus] (stride N : (Fin nX) → ℕ)
local notation "refined" => residueRefinedPeriod spatialModulus stride
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod refined)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod spatialModulus stride)) → PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1))
  (allocatedPrincipalSides B U b S))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod spatialModulus stride)) {M : ℕ} (hM : 0 < M) (selection : Fin (s + 1) ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable {W τ ξ mesh : ℝ} (hW : 0 ≤ W) (base : (Fin nX) → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
local notation "window" => spatialWindow (α := Fin (s + 1)) (trimmedSpatialRootScale τ N stride) 4
local notation "widths" => narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
local notation "reconstruct" => allocatedWholeResidueReconstruction B U b S (Fin nX) spatialModulus stride wholeReference x base label
local notation "volume" => ∏ z, ∏ i, physicalSpatialOutputScale (Fin (s + 1))
  (trimmedSpatialRootScale τ N stride z) (trimmedSpatialSlopeScale W τ N stride z) S.value i
local notation "terms" => ((Fin nX) → SpatialSiteLabel (Fin (s + 1)) spatialModulus 4 mesh)
local notation "twist" => allocatedRecenteredSpatialTwist (τ := τ) B U b S (Fin nX) spatialModulus stride wholeReference x N mesh base label

variable [∀ i, NeZero (N i)]
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (wholeReference label)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (wholeReference label)
local notation "windowMask" => (fun acell : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride =>
  physicalResidueWindowSiteMask root dirs base
    (boundedColumnResidueRepresentative stride acell) stride (trimmedSpatialRootScale τ N stride) 4)
attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem AllocatedModelPhysicalExpansionIdentity.exists_normalized_native_model_of_transfer
    (g : (Finset (Fin (s + 1)) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) →
      T → (∀ a, (e a).Term) → Finset (Fin (s + 1)) → LongSpace × GridSpace → ℂ)
    (hidentity : AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm g)
    {L : ℝ≥0} (hg : ∀ label i k site, LipschitzWith L (g label i k site))
    (hgb : ∀ label i k site z, ‖g label i k site z‖ ≤ 1)
    {Nt V Cc Hs : {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {Lg : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a))
    (Vmax : ℝ≥0) (hVmax : ∀ a, V a ≤ Vmax)
    (hstride : ∀ z, 0 < stride z) (hmesh : 0 < mesh) (hmargin : 3 + 2 * mesh ≤ 4)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hperiod : integerScalarLattice (Unit ⊕ Fin (s + 1)) (spatialModulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection))
    (hV : ∀ z, 0 < widths z) (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z)
    (signal : ((Fin nX) → ℤ) → ℂ)
    (hsignal : ∀ u ∈ integerBox N, ‖signal u‖ ≤ 1)
    (hzero : ∀ u, u ∉ integerBox N → signal u = 0)
    (hτ : 0 < τ)
    {pGain Emodel Espatial Eerror Znormalizer Pvolume : ℝ}
    (hpGain : 0 ≤ pGain) (hEmodel : 0 ≤ Emodel) (hEspatial : 0 ≤ Espatial)
    (hEerror : pGain + 32 ≤ Eerror) (hZnormalizer : 1 / 2 ≤ Znormalizer)
    (hPvolume : 0 ≤ Pvolume)
    (hdim : (nX : ℝ) ≤ pGain + 8 + Emodel + Espatial + Pvolume)
    (hvolumeRatio : (integerBoxCubeCount N (s + 1) : ℝ) / volume ≤ Real.exp Pvolume)
    (hmass : (∑ label : Finset (Fin (s + 1)) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ i, ∑ k,
      ‖((2 : ℂ) ^ Fintype.card (Finset (Fin (s + 1))) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) *
        coverSiteCoefficient e k‖) ≤ Real.exp Emodel)
    (hspatial : allocatedSpatialCoefficientCap (Fin nX) selection M spatialModulus mesh ≤ Real.exp Espatial)
    (hpositive : Znormalizer * (Real.exp (-pGain) / 2 - Real.exp (-Eerror) - Real.exp (-Eerror)) -
      Real.exp (-Eerror) - Real.exp (-Eerror) ≤ (allocatedRecenteredFiniteModelSource (τ := τ) (ξ := ξ) (mesh := mesh)
      B U b S x y₀ q d period r hr hb o bW e a f p hm spatialModulus stride N wholeReference label
      hM selection hx hW base cells (integerSelfSiteTest (s + 1) signal)).re)
    {pGeometry Ecoarse analytic : ℝ}
    (hpGeometry : 0 ≤ pGeometry) (hEcoarse : 0 ≤ Ecoarse) (hanalytic : 0 ≤ analytic)
    (hGGeometry : (Fintype.card G : ℝ) ≤ pGeometry)
    (hXGeometry : (nX : ℝ) ≤ pGeometry) (hdimGeometry : ((s + 2 : ℕ) : ℝ) ≤ pGeometry)
    (hMGeometry : (M : ℝ) ≤ Real.exp pGeometry) (hmodulusGeometry : spatialModulus ≤ M ^ (m + 1))
    (hmeshEarly : mesh = allocatedEarlyRecenteredMesh (Fin nX) selection M spatialModulus pGeometry Ecoarse)
    (hstrideGeometry : ∀ i, (stride i : ℝ) ≤ Real.exp pGeometry)
    (hτGeometry : 1 / τ ≤ Real.exp pGeometry)
    (hLanalytic : ((L * (period * Vmax ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a}) : ℝ≥0) : ℝ) ≤ Real.exp analytic) :
    let Psource := pGain + 8 + Emodel + Espatial
    let A := Classical.choose (exists_allocatedRecenteredFactor_normalization.{uG,uI,uB,uJ,0,uJ} m (s + 1))
    ∃ twistData : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
      (Real.exp (((m + 1 : ℕ) : ℝ) * pGeometry + Fintype.card (Fin nX) * pGeometry))
      (period * (Vmax : ℝ) ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a})
      ⟨Real.exp ((pGeometry + Ecoarse + analytic + A) ^ A), Real.exp_nonneg _⟩,
    ∃ Fnative : integerBox N → ℂ,
      Nonempty (NativeSampleModel (fun _ : Fin nX => 1) s
        ((Psource + Pvolume + 2) ^ Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s))
        (fun u : integerBox N => u.val) Fnative) ∧
      Real.exp (-((Psource + Pvolume + 2) ^ Classical.choose
        (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s))) ≤
        ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) (integerBox_nonempty N)).correlation
          (fun u => signal u.val) (fun u => star (twistData.eval N p u.val) * Fnative u)‖ := by
  intro Psource A
  obtain ⟨cover, hcover, hcoverBound, hperiodPos, hperiodBound, mask, H, hmask, hH, hLip,
      hψ, Vnative, hVnative, hcorrelation⟩ :=
    hidentity.exists_normalized_native_source_of_transfer
      B U b S x y₀ q d period r hr hb o bW e a f p hm
      spatialModulus stride N wholeReference label hM selection hx hW base cells g hg hgb he Vmax hVmax
      hstride hmesh hmargin hbudget hperiod hV hZ signal hsignal hzero hτ
      hpGain hEmodel hEspatial hEerror hZnormalizer hPvolume hdim hvolumeRatio hmass hspatial hpositive
      hpGeometry hEcoarse hanalytic hGGeometry hXGeometry hdimGeometry hMGeometry hmodulusGeometry
      hmeshEarly hstrideGeometry hτGeometry hLanalytic
  let twistData : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
      (Real.exp (((m + 1 : ℕ) : ℝ) * pGeometry + Fintype.card (Fin nX) * pGeometry))
      (period * (Vmax : ℝ) ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a})
      ⟨Real.exp ((pGeometry + Ecoarse + analytic + A) ^ A), Real.exp_nonneg _⟩ := {
    modulus := residueRefinedPeriod spatialModulus stride
    modulus_pos := hperiodPos
    modulus_bound := hperiodBound
    cover := cover
    cover_pos := hcover
    cover_bound := hcoverBound
    mask := mask
    mask_bound := hmask
    smooth := H
    smooth_bound := hH
    smooth_lipschitz := hLip }
  refine ⟨twistData, ?_⟩
  exact nativeCorrelation_restrict_model (integerBox N) (integerBox_nonempty N)
    (fun _ : Fin nX => 1) s _ id signal (twistData.eval N p) Vnative hVnative

theorem AllocatedModelPhysicalExpansionIdentity.exists_canonical_normalized_native_model_of_transfer
    (g : (Finset (Fin (s + 1)) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) →
      T → (∀ a, (e a).Term) → Finset (Fin (s + 1)) → LongSpace × GridSpace → ℂ)
    (hidentity : AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm g)
    {L : ℝ≥0} (hg : ∀ label i k site, LipschitzWith L (g label i k site))
    (hgb : ∀ label i k site z, ‖g label i k site z‖ ≤ 1)
    {Nt V Cc Hs : {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {Lg : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a))
    (Vmax : ℝ≥0) (hVmax : ∀ a, V a ≤ Vmax)
    (hstride : ∀ z, 0 < stride z)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hV : ∀ z, 0 < widths z) (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z)
    (signal : ((Fin nX) → ℤ) → ℂ)
    (hsignal : ∀ u ∈ integerBox N, ‖signal u‖ ≤ 1)
    (hzero : ∀ u, u ∉ integerBox N → signal u = 0)
    (hτ : 0 < τ)
    {pGain Emodel Espatial Eerror Znormalizer Pvolume : ℝ}
    (hpGain : 0 ≤ pGain) (hEmodel : 0 ≤ Emodel) (hEspatial : 0 ≤ Espatial)
    (hEerror : pGain + 32 ≤ Eerror) (hZnormalizer : 1 / 2 ≤ Znormalizer)
    (hPvolume : 0 ≤ Pvolume)
    (hdim : (nX : ℝ) ≤ pGain + 8 + Emodel + Espatial + Pvolume)
    (hmass : (∑ label : Finset (Fin (s + 1)) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ i, ∑ k,
      ‖((2 : ℂ) ^ Fintype.card (Finset (Fin (s + 1))) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) *
        coverSiteCoefficient e k‖) ≤ Real.exp Emodel)
    (hpositive : Znormalizer * (Real.exp (-pGain) / 2 - Real.exp (-Eerror) - Real.exp (-Eerror)) -
      Real.exp (-Eerror) - Real.exp (-Eerror) ≤ (allocatedRecenteredFiniteModelSource (τ := τ) (ξ := ξ) (mesh := mesh)
      B U b S x y₀ q d period r hr hb o bW e a f p hm spatialModulus stride N wholeReference label
      hM selection hx hW base cells (integerSelfSiteTest (s + 1) signal)).re)
    {pGeometry Ecoarse analytic : ℝ}
    (hpGeometry : 0 ≤ pGeometry) (hEcoarse : 0 ≤ Ecoarse) (hanalytic : 0 ≤ analytic)
    (hGGeometry : (Fintype.card G : ℝ) ≤ pGeometry)
    (hXGeometry : (nX : ℝ) ≤ pGeometry) (hdimGeometry : ((s + 2 : ℕ) : ℝ) ≤ pGeometry)
    (hMGeometry : (M : ℝ) ≤ Real.exp pGeometry)
    (hWGeometry : W ≤ Real.exp pGeometry * S.value)
    (hvolumeLog : allocatedAmbientNormalizationLog (s + 1) (nX : ℝ) pGeometry pGeometry pGeometry ≤ Pvolume)
    (hcanonical : spatialModulus = kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hx m))
    (hspatialLog : coarseSpatialPartitionLog (allocatedEarlyCoarseInput m (s + 1) (pGeometry + Ecoarse)) ≤ Espatial)
    (hmeshEarly : mesh = allocatedEarlyRecenteredMesh (Fin nX) selection M spatialModulus pGeometry Ecoarse)
    (hstrideGeometry : ∀ i, (stride i : ℝ) ≤ Real.exp pGeometry)
    (hτGeometry : 1 / τ ≤ Real.exp pGeometry)
    (hLanalytic : ((L * (period * Vmax ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a}) : ℝ≥0) : ℝ) ≤ Real.exp analytic) :
    let Psource := pGain + 8 + Emodel + Espatial
    let A := Classical.choose (exists_allocatedRecenteredFactor_normalization.{uG,uI,uB,uJ,0,uJ} m (s + 1))
    ∃ twistData : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
      (Real.exp (((m + 1 : ℕ) : ℝ) * pGeometry + Fintype.card (Fin nX) * pGeometry))
      (period * (Vmax : ℝ) ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a})
      ⟨Real.exp ((pGeometry + Ecoarse + analytic + A) ^ A), Real.exp_nonneg _⟩,
    ∃ Fnative : integerBox N → ℂ,
      Nonempty (NativeSampleModel (fun _ : Fin nX => 1) s
        ((Psource + Pvolume + 2) ^ Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s))
        (fun u : integerBox N => u.val) Fnative) ∧
      Real.exp (-((Psource + Pvolume + 2) ^ Classical.choose
        (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s))) ≤
        ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) (integerBox_nonempty N)).correlation
          (fun u => signal u.val) (fun u => star (twistData.eval N p u.val) * Fnative u)‖ := by
  have hvolume := (physicalAmbientVolume_log_bound (s + 1) N stride hW
    (by exact_mod_cast Nat.succ_le_of_lt S.positive : (1 : ℝ) ≤ S.value)
    hpGeometry hpGeometry hpGeometry hWGeometry
    (by simp only [Fintype.card_fin]; exact le_rfl : (Fintype.card (Fin nX) : ℝ) ≤ nX)
    (fun i => Nat.pos_of_ne_zero (NeZero.ne (N i))) hstride hτ hstrideGeometry hτGeometry).2
  have hvolumeRatio : (integerBoxCubeCount N (s + 1) : ℝ) / volume ≤ Real.exp Pvolume :=
    hvolume.trans (Real.exp_le_exp.mpr hvolumeLog)
  have hmodulusGeometry : spatialModulus ≤ M ^ (m + 1) := by
    rw [hcanonical]
    exact kernelPeriodCandidate_le _ _
  have hperiod : integerScalarLattice (Unit ⊕ Fin (s + 1)) (spatialModulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection) := by
    rw [hcanonical]
    exact (goodKernelUniformCandidate_spec.{0,uG,0} selection x hx m).1 _
  have hpartition := allocatedEarlyRecenteredMesh_partition_budget m (Fin nX) selection
    hpGeometry hEcoarse hGGeometry (by simpa using hXGeometry) hM hMGeometry hmodulusGeometry
  rw [← hmeshEarly] at hpartition
  have hmargin : 3 + 2 * mesh ≤ 4 := by linarith only [hpartition.2.1]
  have hspatial := hpartition.2.2.2.trans (Real.exp_le_exp.mpr hspatialLog)
  exact hidentity.exists_normalized_native_model_of_transfer
    B U b S x y₀ q d period r hr hb o bW e a f p hm
    spatialModulus stride N wholeReference label hM selection hx hW base cells g hg hgb he Vmax hVmax
    hstride hpartition.1 hmargin hbudget hperiod hV hZ signal hsignal hzero hτ
    hpGain hEmodel hEspatial hEerror hZnormalizer hPvolume hdim hvolumeRatio hmass hspatial hpositive
    hpGeometry hEcoarse hanalytic hGGeometry hXGeometry hdimGeometry hMGeometry hmodulusGeometry
    hmeshEarly hstrideGeometry hτGeometry hLanalytic

theorem AllocatedModelPhysicalExpansionIdentity.exists_uniform_canonical_normalized_native_model_of_transfer
    (g : (Finset (Fin (s + 1)) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) →
      T → (∀ a, (e a).Term) → Finset (Fin (s + 1)) → LongSpace × GridSpace → ℂ)
    (hidentity : AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm g)
    {L : ℝ≥0} (hg : ∀ label i k site, LipschitzWith L (g label i k site))
    (hgb : ∀ label i k site z, ‖g label i k site z‖ ≤ 1)
    {Nt V Cc Hs : {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {Lg : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a))
    (Vmax : ℝ≥0) (hVmax : ∀ a, V a ≤ Vmax)
    (hstride : ∀ z, 0 < stride z)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hV : ∀ z, 0 < widths z) (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z)
    (signal : ((Fin nX) → ℤ) → ℂ)
    (hsignal : ∀ u ∈ integerBox N, ‖signal u‖ ≤ 1)
    (hzero : ∀ u, u ∉ integerBox N → signal u = 0)
    (hτ : 0 < τ)
    {pGain Emodel Espatial Eerror Znormalizer Pvolume : ℝ}
    (hpGain : 0 ≤ pGain) (hEmodel : 0 ≤ Emodel) (hEspatial : 0 ≤ Espatial)
    (hEerror : pGain + 32 ≤ Eerror) (hZnormalizer : 1 / 2 ≤ Znormalizer)
    (hPvolume : 0 ≤ Pvolume)
    (hdim : (nX : ℝ) ≤ pGain + 8 + Emodel + Espatial + Pvolume)
    (hmass : (∑ label : Finset (Fin (s + 1)) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ i, ∑ k,
      ‖((2 : ℂ) ^ Fintype.card (Finset (Fin (s + 1))) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) *
        coverSiteCoefficient e k‖) ≤ Real.exp Emodel)
    (hpositive : Znormalizer * (Real.exp (-pGain) / 2 - Real.exp (-Eerror) - Real.exp (-Eerror)) -
      Real.exp (-Eerror) - Real.exp (-Eerror) ≤ (allocatedRecenteredFiniteModelSource (τ := τ) (ξ := ξ) (mesh := mesh)
      B U b S x y₀ q d period r hr hb o bW e a f p hm spatialModulus stride N wholeReference label
      hM selection hx hW base cells (integerSelfSiteTest (s + 1) signal)).re)
    {pGeometry Ecoarse analytic : ℝ}
    (hpGeometry : 0 ≤ pGeometry) (hEcoarse : 0 ≤ Ecoarse) (hanalytic : 0 ≤ analytic)
    (hGGeometry : (Fintype.card G : ℝ) ≤ pGeometry)
    (hXGeometry : (nX : ℝ) ≤ pGeometry) (hdimGeometry : ((s + 2 : ℕ) : ℝ) ≤ pGeometry)
    (hMGeometry : (M : ℝ) ≤ Real.exp pGeometry)
    (hWGeometry : W ≤ Real.exp pGeometry * S.value)
    (hvolumeLog : allocatedAmbientNormalizationLog (s + 1) (nX : ℝ) pGeometry pGeometry pGeometry ≤ Pvolume)
    (hcanonical : spatialModulus = kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hx m))
    (hspatialLog : coarseSpatialPartitionLog (allocatedEarlyCoarseInput m (s + 1) (pGeometry + Ecoarse)) ≤ Espatial)
    (hmeshEarly : mesh = allocatedEarlyRecenteredMesh (Fin nX) selection M spatialModulus pGeometry Ecoarse)
    (hstrideGeometry : ∀ i, (stride i : ℝ) ≤ Real.exp pGeometry)
    (hτGeometry : 1 / τ ≤ Real.exp pGeometry)
    (hLanalytic : ((L * (period * Vmax ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a}) : ℝ≥0) : ℝ) ≤ Real.exp analytic)
    {Bbudget : ℝ} (hBbudget : 0 ≤ Bbudget)
    (hGeometryBudget : pGeometry ≤ Bbudget) (hCoarseBudget : Ecoarse ≤ Bbudget)
    (hAnalyticBudget : analytic ≤ Bbudget) (hGainBudget : pGain ≤ Bbudget)
    (hMassBudget : Emodel ≤ Bbudget) (hSpatialBudget : Espatial ≤ Bbudget)
    (hVolumeBudget : Pvolume ≤ Bbudget)
    (hCoverBudget : (period : ℝ) * (Vmax : ℝ) ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} ≤ Real.exp Bbudget) :
    let Anorm := Classical.choose (exists_allocatedRecenteredFactor_normalization.{uG,uI,uB,uJ,0,uJ} m (s + 1))
    let Anative := Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s)
    let A := Classical.choose (exists_normalizedNative_uniform_budget m Anorm Anative)
    let budget := (Bbudget + A) ^ A
    ∃ twistData : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
      (Real.exp budget) (Real.exp budget) ⟨Real.exp budget, Real.exp_nonneg _⟩,
      ∃ Fnative : integerBox N → ℂ,
        Nonempty (NativeSampleModel (fun _ : Fin nX => 1) s budget
          (fun u : integerBox N => u.val) Fnative) ∧
        Real.exp (-budget) ≤
          ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) (integerBox_nonempty N)).correlation
            (fun u => signal u.val) (fun u => star (twistData.eval N p u.val) * Fnative u)‖ := by
  intro Anorm Anative A budget
  have hnumeric := (Classical.choose_spec (exists_normalizedNative_uniform_budget m Anorm Anative)).2
    hBbudget ⟨hpGeometry, hGeometryBudget⟩ ⟨hEcoarse, hCoarseBudget⟩ ⟨hanalytic, hAnalyticBudget⟩
    ⟨hpGain, hGainBudget⟩ ⟨hEmodel, hMassBudget⟩ ⟨hEspatial, hSpatialBudget⟩ ⟨hPvolume, hVolumeBudget⟩
    (le_refl Bbudget) (hXGeometry.trans hGeometryBudget)
  have hdetector := hidentity.exists_canonical_normalized_native_model_of_transfer
    B U b S x y₀ q d period r hr hb o bW e a f p hm
    spatialModulus stride N wholeReference label hM selection hx hW base cells g hg hgb he Vmax hVmax
    hstride hbudget hV hZ signal hsignal hzero hτ
    hpGain hEmodel hEspatial hEerror hZnormalizer hPvolume hdim hmass hpositive
    hpGeometry hEcoarse hanalytic hGGeometry hXGeometry hdimGeometry hMGeometry hWGeometry hvolumeLog hcanonical hspatialLog
    hmeshEarly hstrideGeometry hτGeometry hLanalytic
  apply normalized_native_detection_mono N p (fun u : integerBox N => u.val)
    (FiniteProbabilityWeights.uniformFinset (integerBox N) (integerBox_nonempty N))
    (fun u => signal u.val) s ?_ ?_ ?_ hnumeric.2.2.2 hdetector
  · apply Real.exp_le_exp.mpr
    simpa only [Fintype.card_fin] using hnumeric.1
  · exact hCoverBudget.trans (Real.exp_le_exp.mpr hnumeric.2.1)
  · exact Real.exp_le_exp.mpr hnumeric.2.2.1

end Erdos3.VectorPolynomial

end

end OAI
