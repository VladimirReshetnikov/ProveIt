import OAI.Combinatorics.Progressions.Estimates.AllocatedProductIdealCutoff

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)
variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "single" => (fun _ : Fin m => Unit)
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "siteChart" => mixedCoveredJetChart (O := single) U o b hb bW d
local notation "siteRegion" => mixedCoveredJetRegion (O := single) (E := E) U o b d
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "pointCap" => (fun j => C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))

include hR hC hchart in
theorem allocatedProductSiteCutoff_small_representatives
    (y : EuclideanJetLayers U rowTypes)
    (hne : allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr y ≠ 0) :
    ∃ w : Finset α → MixedCoveredJetSource I single E n d,
      (∀ s, siteChart (w s) = coveredRowsSiteValue rowSets U y s) ∧
      (∀ s j, ‖normalizedLatticePoint (euclideanSubspace (U j)) (b j)
        (mixedCoveredJetCoordinates U o d (w s) j ()).1‖ ≤ pointCap j) := by
  have hs (s : Finset α) : allocatedBufferedSiteChartFactor B U b S o hb bW d r hr (fun _ => 1)
      (coveredRowsSiteValue rowSets U y s) ≠ 0 := by
    intro he
    apply hne
    unfold allocatedProductSiteCutoff
    exact Finset.prod_eq_zero (Finset.mem_univ s) he
  have hex (s : Finset α) : ∃ w : MixedCoveredJetSource I single E n d,
      siteChart w = coveredRowsSiteValue rowSets U y s ∧
      ∀ j, ‖normalizedLatticePoint (euclideanSubspace (U j)) (b j)
        (mixedCoveredJetCoordinates U o d w j ()).1‖ ≤ pointCap j := by
    have hmem : coveredRowsSiteValue rowSets U y s ∈ siteChart '' siteRegion := by
      by_contra he
      apply hs s
      unfold allocatedBufferedSiteChartFactor
      exact restrictedComplexChartDensity_zero _ _ _ _ he
    obtain ⟨w, hw, hwy⟩ := hmem
    have hraw : allocatedBufferedMixedSiteFactor B U b S r hr (fun _ => 1)
        (fun j => mixedArrayRegroup _ _ _ (w.1 j) ()) ≠ 0 := by
      intro he
      apply hs s
      rw [← hwy, allocatedBufferedSiteChartFactor, restrictedComplexChartDensity_apply _ _ _ _
        (mixedCoveredJetChart_injOn U o b hb bW d
          (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
          (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))) hw,
        Complex.ofReal_one, one_mul, he]
    refine ⟨w, hwy, ?_⟩
    intro j
    exact allocatedBufferedMixedSiteFactor_nonzero_point_bound B U b S r hr (fun _ => 1)
      hR o (fun j => mixedArrayRegroup _ _ _ (w.1 j) ()) hraw C hC hchart j
  choose w hw hp using hex
  exact ⟨w, hw, hp⟩

include hR hC hchart in
theorem allocatedProductSiteCutoff_sites_quarter
    (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) * pointCap j) ≤ 1 / 4)
    (z : MixedCoveredJetSource I rowTypes E n d)
    (hz : z ∈ mixedCoveredJetRegion (E := E) U o b d
      (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j)))
    (hne : allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr (chart z) ≠ 0)
    (s : Finset α) :
    mixedCoveredRowsSiteValue rowSets d z s ∈ siteRegion := by
  obtain ⟨w, hw, hp⟩ := allocatedProductSiteCutoff_small_representatives B U b S rowSets o hb bW d r hr
    hR C hC hchart (chart z) hne
  apply mixedCoveredRowsOfSites_reconstructed_quarter rowSets d U o b hb bW z hz w hw pointCap _ hp hbudget s
  intro j
  exact mul_nonneg (hC j) (mul_nonneg (by positivity) (mul_nonneg (by positivity) (hR j).le))

end Erdos3.VectorPolynomial

end

end OAI
