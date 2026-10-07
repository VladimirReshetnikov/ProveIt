import OAI.Combinatorics.Progressions.Estimates.AllocatedFiniteModelPhysicalExpansion

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
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
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

theorem exists_allocated_chart_ideal_ambient_lift
    (hdiv : period ∣ d)
    (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    {T : Type*} [Fintype T] (a : T → ℂ)
    (f : T → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ) {L : ℝ≥0}
    (hf : ∀ k s, LipschitzWith L (f k s)) (hf1 : ∀ k s z, ‖f k s z‖ ≤ 1) :
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Lcut := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) * Lcoord
    let Lsite := Lcut * d + max (L * Lcoord * period) (4 * period) * (d / period : ℕ)
    let Lrows := ∑ j : Fin m, ((rowSets j).card : ℝ≥0)
    let mass := ∑ label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)),
      ∑ k, ‖(2 : ℂ) ^ Fintype.card (Finset α) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label k‖₊
    ∃ F : (JetAmbientIndex rowTypes J → UnitAddCircle) → ℂ,
      LipschitzWith (mass * (Fintype.card (Finset α) * (Lsite * Lrows))) F ∧
      (∀ z, ‖F z‖ ≤ mass) ∧
      ∀ y : EuclideanJetLayers U rowTypes,
        allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y =
          F (coveredJetAmbientTorus U 1 y) := by
  intro Lcoord Lcut Lsite Lrows mass
  let Label := Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))
  have hex (label : Label) (k : T) (s : Finset α) :=
    exists_allocated_masked_ambient_lift B U b S o hb bW d r hr period
      hdiv hR C hC hchart hbudget Cforward hforward K hK (label s) (f k s) (hf k s) (hf1 k s)
  choose g hg hgb hgv using hex
  let c := fun t : Label × T => (2 : ℂ) ^ Fintype.card (Finset α) *
    allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a t.1 t.2
  let v := fun t : Label × T => fun z : JetAmbientIndex rowTypes J → UnitAddCircle =>
    ∏ s, g t.1 t.2 s (rowsAmbientSite rowSets s z)
  have hv (t : Label × T) : (∀ z, ‖v t z‖ ≤ 1) ∧
      LipschitzWith (Fintype.card (Finset α) * (Lsite * Lrows)) (v t) := by
    have h := bounded_lipschitz_fintype_prod
      (fun s z => g t.1 t.2 s (rowsAmbientSite rowSets s z)) (B := 1) le_rfl
      (fun s => (hg t.1 t.2 s).comp (rowsAmbientSite_lipschitz rowSets s))
      (fun s z => hgb t.1 t.2 s _)
    simpa only [one_pow, mul_one, NNReal.coe_one] using h
  have hsum := finite_lipschitz_linear_combination c v (fun t => (hv t).2) (B := 1)
    (fun t z => (hv t).1 z)
  have hm : (∑ t, ‖c t‖₊) = mass := by
    rw [Fintype.sum_prod_type]
  rw [hm, mul_one] at hsum
  refine ⟨fun z => ∑ t, c t * v t z, hsum.2, hsum.1, ?_⟩
  intro y
  simp only [Fintype.sum_prod_type]
  unfold allocatedProductChartIdealApproximation
  apply Finset.sum_congr rfl
  intro label _
  apply Finset.sum_congr rfl
  intro k _
  dsimp only [c, v]
  simp_rw [hgv, rowsAmbientSite_eq U rowSets]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ]
  ring

end Erdos3.VectorPolynomial

end

end OAI
