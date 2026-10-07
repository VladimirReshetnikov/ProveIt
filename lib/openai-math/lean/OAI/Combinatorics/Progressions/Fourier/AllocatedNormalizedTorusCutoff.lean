/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.AllocatedBufferedAmbientCutoff
import OAI.Combinatorics.Progressions.Estimates.AllocatedCanonicalNormalizer

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ} (r : ℝ≥0) (hr : 0 < r)
local notation "ambient" => JetAmbientIndex (fun _ : Fin m => Unit) J

noncomputable def allocatedBufferedTorusCutoff : (ambient → UnitAddCircle) → ℝ :=
  smallBoxTorusKernel (allocatedBufferedAmbientCutoff (R := R) U b o r hr)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)

include hR hC hchart hbudget in
theorem allocatedBufferedTorusCutoff_range (x : ambient → UnitAddCircle) :
    0 ≤ allocatedBufferedTorusCutoff (R := R) U b o r hr x ∧
      allocatedBufferedTorusCutoff (R := R) U b o r hr x ≤ 1 := by
  apply smallBoxTorusKernel_range _ zero_le_one (allocatedBufferedAmbientCutoff_range U b o r hr)
  intro z hz i
  exact (allocatedBufferedAmbientCutoff_support U b o r hr hR C hC hchart hbudget z hz i).trans_lt (by norm_num)

include hR hC hchart hbudget in
theorem allocatedBufferedTorusCutoff_lipschitz
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K) :
    LipschitzWith ((Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) *
      (K * ∑ j, Cforward j * Fintype.card (J j))) (allocatedBufferedTorusCutoff (R := R) U b o r hr) := by
  apply smallBoxTorusKernel_lipschitz _
    (allocatedBufferedAmbientCutoff_lipschitz U b o r hr hR Cforward hforward K hK)
    (fun z => (allocatedBufferedAmbientCutoff_range U b o r hr z).1)
  intro z hz i
  exact (allocatedBufferedAmbientCutoff_support U b o r hr hR C hC hchart hbudget z hz i).trans_lt (by norm_num)

include hR hC hchart hbudget in
theorem allocatedBufferedTorusCutoff_local (z : ambient → ℝ) (hz : ∀ i, |z i| < 1 / 2) :
    allocatedBufferedTorusCutoff (R := R) U b o r hr (fun i => (z i : UnitAddCircle)) =
      allocatedBufferedAmbientCutoff (R := R) U b o r hr z := by
  apply smallBoxTorusKernel_local _ _ z hz
  intro v hv i
  exact (allocatedBufferedAmbientCutoff_support U b o r hr hR C hC hchart hbudget v hv i).trans_lt (by norm_num)

include hR hC hchart hbudget in
theorem allocatedBufferedTorusCutoff_zero_outside_quarter (x : ambient → UnitAddCircle)
    (hx : ∃ i, 1 / 4 < ‖x i‖) : allocatedBufferedTorusCutoff (R := R) U b o r hr x = 0 :=
  smallBoxTorusKernel_zero_outside_quarter _
    (allocatedBufferedAmbientCutoff_support U b o r hr hR C hC hchart hbudget) x hx

variable {G : Type*} [Fintype G]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

include hR hC hchart hbudget in
theorem allocatedBufferedTorusCutoff_eq_siteChart
    (y : EuclideanJetLayers U (fun _ => Unit)) :
    (allocatedBufferedTorusCutoff (R := R) U b o r hr (coveredJetAmbientTorus U d y) : ℂ) =
      allocatedBufferedSiteChartFactor B U b S o hb bW d r hr (fun _ => 1) y := by
  let chart := mixedCoveredJetChart (O := fun _ => Unit) U o b hb bW d
  let region := mixedCoveredJetRegion (O := fun _ => Unit) (E := E) U o b d
    (fun j _ => standardLatticeSmallBox (J j))
  rw [allocatedBufferedSiteChartFactor_enlarge B U b S o hb bW d r hr (fun _ => 1)
    hR C hC hchart hbudget (fun j _ => standardLatticeSmallBox (J j))
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j)) (fun _ _ => Set.Subset.rfl)]
  by_cases hy : y ∈ chart '' region
  · obtain ⟨w, hw, rfl⟩ := hy
    rw [restrictedComplexChartDensity_apply _ _ _ _
      (mixedCoveredJetChart_injOn U o b hb bW d _ (fun _ _ => Set.Subset.rfl)) hw,
      Complex.ofReal_one, one_mul, coveredJetAmbientTorus_chart U b hb o bW d w]
    have hs : ∀ i, |mixedJetAmbientPoint U b o w.1 i| < 1 / 2 := by
      rintro ⟨j, t, i⟩
      exact (hw j (Set.mem_univ j) t (Set.mem_univ t)).1 i
    rw [allocatedBufferedTorusCutoff_local U b o r hr hR C hC hchart hbudget _ hs]
    unfold allocatedBufferedAmbientCutoff allocatedBufferedMixedSiteFactor bufferedCoordinateProjection
    rw [allocatedFullAmbientSiteCoordinates_point, mul_one]
  · rw [restrictedComplexChartDensity_zero _ _ _ _ hy]
    suffices hz : allocatedBufferedTorusCutoff (R := R) U b o r hr (coveredJetAmbientTorus U d y) = 0 by
      rw [hz, Complex.ofReal_zero]
    by_contra hn
    obtain ⟨v, hv, he, _⟩ := smallBoxTorusKernel_nonzero_quarter_lift _
      (allocatedBufferedAmbientCutoff_support U b o r hr hR C hC hchart hbudget)
      (coveredJetAmbientTorus U d y) hn
    exact hy (coveredJetAmbientTorus_smallBox_mem_chart U b hb o bW d y v
      (fun i => congrFun he i) (fun i => (hv i).trans_lt (by norm_num)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ}

local notation "single" => (fun _ : Fin m => Unit)
local notation "ambient" => JetAmbientIndex single J

variable (r : ℝ≥0) (hr : 0 < r)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rowAmbient" => JetAmbientIndex rowTypes J

noncomputable def allocatedProductTorusCutoff (z : rowAmbient → UnitAddCircle) : ℝ :=
  ∏ s : Finset α, allocatedBufferedTorusCutoff (R := R) U b o r hr (rowSiteAmbientTorus rowSets s z)

include hR hC hchart hbudget in
theorem allocatedProductTorusCutoff_range (z : rowAmbient → UnitAddCircle) :
    0 ≤ allocatedProductTorusCutoff (R := R) U b o r hr rowSets z ∧
      allocatedProductTorusCutoff (R := R) U b o r hr rowSets z ≤ 1 := by
  constructor
  · exact Finset.prod_nonneg (fun s _ => (allocatedBufferedTorusCutoff_range U b o r hr hR C hC hchart hbudget _).1)
  · exact Finset.prod_le_one₀ (fun s _ => (allocatedBufferedTorusCutoff_range U b o r hr hR C hC hchart hbudget _).1)
      (fun s _ => (allocatedBufferedTorusCutoff_range U b o r hr hR C hC hchart hbudget _).2)

include hR hC hchart hbudget in
theorem allocatedProductTorusCutoff_lipschitz (D : Fin m → ℝ≥0)
    (hD : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ D j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K) :
    LipschitzWith (Fintype.card (Finset α) *
      (((Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) *
        (K * ∑ j, D j * Fintype.card (J j))) * ∑ j, ((rowSets j).card : ℝ≥0)))
      (allocatedProductTorusCutoff (R := R) U b o r hr rowSets) := by
  let f := fun s (z : rowAmbient → UnitAddCircle) =>
    (allocatedBufferedTorusCutoff (R := R) U b o r hr (rowSiteAmbientTorus rowSets s z) : ℂ)
  have hf (s : Finset α) : LipschitzWith
      (((Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) *
        (K * ∑ j, D j * Fintype.card (J j))) * ∑ j, ((rowSets j).card : ℝ≥0)) (f s) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    rw [Complex.isometry_ofReal.dist_eq]
    exact ((allocatedBufferedTorusCutoff_lipschitz U b o r hr hR C hC hchart hbudget D hD K hK).comp
      (rowSiteAmbientTorus_lipschitz rowSets s)).dist_le_mul z w
  have hbnd (s : Finset α) (z : rowAmbient → UnitAddCircle) : ‖f s z‖ ≤ (1 : ℝ≥0) := by
    have h := allocatedBufferedTorusCutoff_range U b o r hr hR C hC hchart hbudget (rowSiteAmbientTorus rowSets s z)
    simpa only [f, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h.1, NNReal.coe_one] using h.2
  have h := (bounded_lipschitz_fintype_prod f (B := 1) le_rfl hf hbnd).2
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have hd := h.dist_le_mul z w
  simpa only [f, ← Complex.ofReal_prod, Complex.isometry_ofReal.dist_eq,
    one_pow, mul_one, allocatedProductTorusCutoff] using hd

variable {G : Type*} [Fintype G]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

include hR hC hchart hbudget in
theorem allocatedProductTorusCutoff_eq (y : EuclideanJetLayers U rowTypes) :
    (allocatedProductTorusCutoff (R := R) U b o r hr rowSets (coveredJetAmbientTorus U d y) : ℂ) =
      allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr y := by
  unfold allocatedProductTorusCutoff allocatedProductSiteCutoff
  rw [Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro s _
  rw [← coveredRowsSiteValue_ambient]
  exact allocatedBufferedTorusCutoff_eq_siteChart U b o r hr hR C hC hchart hbudget B S hb bW d _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ}

local notation "single" => (fun _ : Fin m => Unit)
local notation "ambient" => JetAmbientIndex single J

variable (r : ℝ≥0) (hr : 0 < r)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rowAmbient" => JetAmbientIndex rowTypes J

variable {G : Type*} [Fintype G]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "amp" => ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖
local notation "ampN" => ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖₊

noncomputable def allocatedNormalizedProductTorusCutoff (z : rowAmbient → UnitAddCircle) : ℝ :=
  amp * allocatedProductTorusCutoff (R := R) U b o r hr rowSets z

omit [∀ j, Fintype (E j)] [NeZero d] in
include hR hC hchart hbudget in
theorem allocatedNormalizedProductTorusCutoff_range (z : rowAmbient → UnitAddCircle) :
    0 ≤ allocatedNormalizedProductTorusCutoff U b o r hr rowSets B S z ∧
      allocatedNormalizedProductTorusCutoff U b o r hr rowSets B S z ≤ amp := by
  have h := allocatedProductTorusCutoff_range U b o r hr hR C hC hchart hbudget rowSets z
  exact ⟨mul_nonneg (norm_nonneg _) h.1,
    (mul_le_mul_of_nonneg_left h.2 (norm_nonneg _)).trans_eq (mul_one _)⟩

include hR hC hchart hbudget in
theorem allocatedNormalizedProductTorusCutoff_pullback (y : EuclideanJetLayers U rowTypes) :
    allocatedNormalizedProductTorusCutoff U b o r hr rowSets B S (coveredJetAmbientTorus U d y) =
      amp * ‖allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr y‖ := by
  have he := congrArg norm (allocatedProductTorusCutoff_eq U b o r hr hR C hC hchart hbudget rowSets B S hb bW d y)
  rw [Complex.norm_real, Real.norm_of_nonneg
    (allocatedProductTorusCutoff_range U b o r hr hR C hC hchart hbudget rowSets _).1] at he
  exact congrArg (fun z => amp * z) he

variable (D : Fin m → ℝ≥0)
variable (hD : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ D j * ‖v‖)
variable (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
local notation "cutoffL" => (Fintype.card (Finset α) *
  (((Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) *
    (K * ∑ j, D j * Fintype.card (J j))) * ∑ j, (Finset.card (rowSets j) : ℝ≥0)))

omit [∀ j, Fintype (E j)] [NeZero d] in
include hR hC hchart hbudget hD hK in
theorem allocatedNormalizedProductTorusCutoff_lipschitz :
    LipschitzWith (ampN * cutoffL) (allocatedNormalizedProductTorusCutoff U b o r hr rowSets B S) := by
  have h := allocatedProductTorusCutoff_lipschitz U b o r hr hR C hC hchart hbudget rowSets D hD K hK
  apply LipschitzWith.of_dist_le_mul
  intro z w
  change |amp * allocatedProductTorusCutoff U b o r hr rowSets z -
    amp * allocatedProductTorusCutoff U b o r hr rowSets w| ≤ _
  rw [← mul_sub, abs_mul, abs_of_nonneg (norm_nonneg _)]
  have hh := mul_le_mul_of_nonneg_left (h.dist_le_mul z w) (norm_nonneg (((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹))
  simpa only [Real.dist_eq, NNReal.coe_mul, coe_nnnorm, mul_assoc] using hh

omit [∀ j, Fintype (E j)] [NeZero d] in
include hR hC hchart hbudget hD hK in
theorem exists_allocated_normalized_cutoff_fourier {δ P : ℝ}
    (hδ : 0 < δ) (hP : 0 ≤ P) (hdim : (Fintype.card rowAmbient : ℝ) ≤ P)
    (hLip : ((ampN * cutoffL : ℝ≥0) : ℝ) ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P) :
    ∃ (F : Type) (inst : Fintype F), let _ : Fintype F := inst
    ∃ (frequency : F → rowAmbient → ℤ) (c : F → ℂ),
      (Fintype.card F : ℝ) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) ∧
      (∀ a i, |(frequency a i : ℝ)| ≤ Real.exp ((2 * P + 2) ^ 4)) ∧
      (∑ a, ‖c a‖) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) * amp ∧
      ∀ z, ‖(allocatedNormalizedProductTorusCutoff U b o r hr rowSets B S z : ℂ) -
        ∑ a, c a * ∏ i, CircleFourier.character (frequency a i • z i)‖ ≤ δ := by
  have h := allocatedNormalizedProductTorusCutoff_lipschitz U b o r hr hR C hC hchart hbudget rowSets B S D hD K hK
  have hl : LipschitzWith (ampN * cutoffL)
      (fun z => (allocatedNormalizedProductTorusCutoff U b o r hr rowSets B S z : ℂ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    rw [Complex.isometry_ofReal.dist_eq]
    exact h.dist_le_mul z w
  apply exists_ambient_torus_fourier_approximation _ (ampN * cutoffL) ampN hl _ hδ hP hdim hLip hδP
  intro z
  have hz := allocatedNormalizedProductTorusCutoff_range U b o r hr hR C hC hchart hbudget rowSets B S z
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hz.1, coe_nnnorm] using hz.2

end Erdos3.VectorPolynomial

end

end OAI
