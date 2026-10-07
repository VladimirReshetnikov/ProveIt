import OAI.Combinatorics.Progressions.Sampling.AllocatedFullGridChartModelMeasurable

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr

theorem allocatedProductSiteCutoff_measurable :
    Measurable (allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr) := by
  unfold allocatedProductSiteCutoff
  apply Finset.measurable_prod
  intro s _
  apply (allocatedBufferedSiteChartFactor_measurable B U b S o hb bW d r hr
    (fun _ => 1) (LipschitzWith.const 1) (fun _ => by simp)).comp
  have hcont : Continuous (fun y : EuclideanJetLayers U rowTypes => coveredRowsSiteValue rowSets U y s) := by
    unfold coveredRowsSiteValue
    fun_prop
  exact hcont.measurable

theorem allocatedProductFullGridPrefactor_measurable (hf : Measurable f) :
    Measurable (allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ f) := by
  unfold allocatedProductFullGridPrefactor
  apply (allocatedProductSiteCutoff_measurable B U b S rowSets d r hr hb o bW).mul
  apply measurable_const.mul
  exact Complex.measurable_ofReal.comp
    (allocatedWholeMaskedGridlessProfile_measurable B U b S x y₀ rows hb o bW d q f hf)

end Erdos3.VectorPolynomial

end

end OAI
