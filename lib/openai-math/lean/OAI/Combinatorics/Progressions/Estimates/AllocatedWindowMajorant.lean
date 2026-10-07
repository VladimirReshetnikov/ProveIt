import OAI.Combinatorics.Progressions.Probability.AllocatedProbabilityMajorantMass
import OAI.Combinatorics.Progressions.Probability.AllocatedWindowProbability

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (p : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a}, PMF (CoefficientJetAxisRow O a.val))

local notation "scale" => (∏ a, allocatedLongJetOutputScale B U b S (O := O) a)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

theorem allocatedGridWindowQuarter_le_majorant
    (selected : {a // allocatedGridAxis (I := I) U b S.value a} → Prop) [DecidablePred selected]
    (W : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a}, Finset (CoefficientJetAxisRow O a.val))
    (hW : ∀ a, selected a → (W a).Nonempty)
    (E : ℝ) (δ A : ℝ≥0)
    (hbudget : E * (∏ a : {a // allocatedGridAxis (I := I) U b S.value a},
      if selected a then ((W a).card : ℝ) else 1) ≤ δ)
    (C V : Fin m → ℝ≥0)
    (hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (y : EuclideanJetLayers U O) :
    restrictedChartDensity (mixedCoveredJetChart U o b hb bW d)
      (mixedCoveredJetRegion (O := O) (E := Q) U o b d
        (fun j _ => standardLatticeClosedQuarterBox (J j))) 1
      (fun z : MixedCoveredJetSource I O Q n d =>
        allocatedGridWindowWeight B U b S O selected W p
          (fun a => coefficientJetAxisEquiv O I n z.1 a.val) *
          (E * A / scale) / coveredJetArrayScale (O := O) U) y ≤
      allocatedProbabilityMajorant B U b S o
        (allocatedGridWindowPMF B U b S O selected W p hW) δ A d y := by
  let aux := allocatedGridWindowPMF B U b S O selected W p hW
  let chart := mixedCoveredJetChart (O := O) U o b hb bW d
  let small := mixedCoveredJetRegion (O := O) (E := Q) U o b d
    (fun j _ => standardLatticeClosedQuarterBox (J j))
  let rawW := fun z : MixedCoveredJetSource I O Q n d =>
    allocatedGridWindowWeight B U b S O selected W p
      (fun a => coefficientJetAxisEquiv O I n z.1 a.val) *
      (E * A / scale) / coveredJetArrayScale (O := O) U
  let rawP := fun z : MixedCoveredJetSource I O Q n d =>
    allocatedProbabilityGridDensity B U b S aux
      (fun a => coefficientJetAxisEquiv O I n z.1 a.val) *
      ((δ : ℝ) * A / scale) / coveredJetArrayScale (O := O) U
  have hs : 0 < scale := Finset.prod_pos
    (fun a _ => allocatedLongJetOutputScale_pos B U b S (O := O) a)
  have hc : 0 < coveredJetArrayScale (O := O) U := coveredJetArrayScale_pos U
  have hraw (z : MixedCoveredJetSource I O Q n d) : rawW z ≤ rawP z := by
    dsimp only [rawW, rawP]
    rw [allocatedGridWindowWeight_eq_probability B U b S O selected W p hW]
    let D := allocatedProbabilityGridDensity B U b S aux
      (fun a => coefficientJetAxisEquiv O I n z.1 a.val)
    let N : ℝ := ∏ a : {a // allocatedGridAxis (I := I) U b S.value a},
      if selected a then ((W a).card : ℝ) else 1
    change (N * D) * (E * A / scale) / coveredJetArrayScale (O := O) U ≤
      D * ((δ : ℝ) * A / scale) / coveredJetArrayScale (O := O) U
    calc
      _ = D * ((E * N) * A / scale) / coveredJetArrayScale (O := O) U := by ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hbudget A.coe_nonneg) hs.le)
          (allocatedProbabilityGridDensity_nonneg B U b S aux _)) hc.le
  have hcompare : restrictedChartDensity chart small 1 rawW y ≤
      restrictedChartDensity chart small 1 rawP y := by
    by_cases hy : y ∈ chart '' small
    · obtain ⟨z, hz, rfl⟩ := hy
      rw [restrictedChartDensity_apply chart small 1 rawW
        (mixedCoveredJetChart_injOn U o b hb bW d _
          (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))) hz,
        restrictedChartDensity_apply chart small 1 rawP
        (mixedCoveredJetChart_injOn U o b hb bW d _
          (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))) hz,
        one_mul, one_mul]
      exact hraw z
    · rw [restrictedChartDensity_zero chart small 1 rawW hy,
        restrictedChartDensity_zero chart small 1 rawP hy]
  exact hcompare.trans
    (allocatedProbabilityQuarter_le_majorant B U b S o aux hb bW d δ A C V hC hV y)

end Erdos3.VectorPolynomial

end

end OAI
