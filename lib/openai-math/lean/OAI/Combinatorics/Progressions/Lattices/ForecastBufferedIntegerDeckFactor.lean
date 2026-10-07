import OAI.Combinatorics.Progressions.Sampling.ActualForecastModelPrecision
import OAI.Combinatorics.Progressions.Sampling.ForecastPhysicalQuarterRecovery

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "single" => (fun _ : Fin m => Unit)

theorem forecastBufferedCoveredSiteFactor_integer_deck
    (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r) {Y : Type*}
    (F : (∀ j, Fin (n j) ⊕ E j → ZMod d) → Y × (LayerSamplerAxis I n → ℝ) → ℂ)
    (s : Y) (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (deck : ∀ j, E j → ℤ)
    (u : ∀ j, euclideanSubspace (U j))
    (hdeck : ∀ j, normalizedLatticeRepresentative (euclideanSubspace (U j)) (b j) (hb j)
        (orthonormalMixedChart (o j) (w j)) + ((bW j).equivFun.symm (deck j)).val = u j)
    (hquarter : ∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (b j)
      (orthonormalMixedChart (o j) (w j)) i| ≤ 1 / 4) :
    let y : EuclideanJetLayers U single := fun j _ => QuotientAddGroup.mk ((d : ℝ)⁻¹ • u j)
    forecastBufferedCoveredSiteFactor B U b S o hb bW d r hr d F s y =
      allocatedBufferedSiteChartFactor B U b S o hb bW d r hr (fun _ => 1) y *
        F (fun j => Sum.elim (fun i => ((w j).2 i : ZMod d))
          (fun i => (deck j i : ZMod d))) (s, allocatedFullMixedSiteValue (R := R) U b w) := by
  let z : MixedCoveredJetSource I single E n d :=
    (fun j => (fun i _ => (w j).1 i, fun i _ => (w j).2 i),
      fun j _ => integerResidueMap (E j) d (deck j))
  have hz : z ∈ mixedCoveredJetRegion (O := single) (E := E) U o b d
      (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j)) := by
    intro j _ t _
    exact ⟨hquarter j, mem_univ _⟩
  have hchart : mixedCoveredJetChart U o b hb bW d z =
      fun j (_ : Unit) => QuotientAddGroup.mk ((d : ℝ)⁻¹ • u j) := by
    funext j t
    exact (normalizedCoveredChart_of_integer_deck (euclideanSubspace (U j)) (bW j) (b j) (hb j)
      d (u j) (orthonormalMixedChart (o j) (w j)) (deck j) (hdeck j)).symm
  have h := forecastBufferedCoveredSiteFactor_on_chart B U b S o hb bW d r hr d F s z hz
  rw [hchart] at h
  have hres : forecastBufferedFullResidue d d z = fun j =>
      Sum.elim (fun i => ((w j).2 i : ZMod d)) (fun i => (deck j i : ZMod d)) := by
    funext j i
    cases i with
    | inl i => rfl
    | inr i => exact ZMod.natCast_zmod_val (deck j i : ZMod d)
  rw [hres] at h
  exact h

end Erdos3.VectorPolynomial

end

end OAI
