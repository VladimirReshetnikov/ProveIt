/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import OAI.Combinatorics.Progressions.Estimates.ComplexNormalizationError
import OAI.Combinatorics.Progressions.Estimates.LowWeightFibers
import OAI.Combinatorics.Progressions.Lattices.SelectedResidueApproximation
import OAI.Combinatorics.Progressions.Probability.PMFPointMassMixture

namespace OAI

section

namespace Erdos3

noncomputable def selectedResidueDensityMass {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (D : (K × I → ℤ) → ℝ) : ℝ :=
  finiteDensityMass (selectedResidueSmoothWeight modulus G V) D

theorem selectedResidueDensityMass_complex {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x) (D : (K × I → ℤ) → ℝ) :
    (selectedResidueDensityMass modulus G V D : ℂ) =
      ∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * (D x : ℂ) := by
  simp only [selectedResidueDensityMass, finiteDensityMass_complex, selectedResidueSmoothPMF_toReal]

noncomputable def selectedResidueDensityPMF {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D) : PMF (K × I → ℤ) :=
  finiteDensityTiltPMF _ (rectangularWeightIndices 0 V 1)
    (selectedResidueSmoothWeight_nonneg modulus G V)
    (selectedResidueSmoothWeight_zero_off modulus G V hV) hZ D hD0 hD

theorem selectedResidueDensityPMF_toReal {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D) (x : K × I → ℤ) :
    (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal =
      (selectedResidueSmoothPMF modulus G V hV hZ x).toReal * D x /
        selectedResidueDensityMass modulus G V D := by
  unfold selectedResidueDensityMass at hD ⊢
  simp only [selectedResidueDensityPMF, finiteDensityTiltPMF_toReal, selectedResidueSmoothPMF_toReal]

theorem selectedResidueDensityPMF_complexMean {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D) (f : (K × I → ℤ) → ℂ) :
    (∑' x, ((selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal : ℂ) * f x) =
      (∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * ((D x : ℂ) * f x)) /
        (selectedResidueDensityMass modulus G V D : ℂ) := by
  unfold selectedResidueDensityMass at hD ⊢
  simp only [selectedResidueDensityPMF, finiteDensityTiltPMF_complexMean,
    selectedResidueSmoothPMF_toReal]

theorem selectedResidueDensityPMF_error {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D) (f : (K × I → ℤ) → ℂ)
    {a : ℂ} {E ε B : ℝ} (hlower : 1 / 2 ≤ selectedResidueDensityMass modulus G V D)
    (herror : ‖(∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) *
      ((D x : ℂ) * f x)) - a‖ ≤ E)
    (hmass : |selectedResidueDensityMass modulus G V D - 1| ≤ ε) (hcap : ‖a‖ ≤ B) :
    ‖(∑' x, ((selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal : ℂ) * f x) - a‖ ≤
      2 * E + 2 * B * ε := by
  rw [selectedResidueDensityPMF_complexMean]
  exact complex_normalization_error hlower herror hmass hcap

end Erdos3

end

section

namespace Erdos3
open MeasureTheory

theorem selectedResidueDensityMass_integral {K I : Type*} [Fintype K] [Fintype I]
    (stride : I → ℕ) (cells : Finset (ColumnResiduePattern K I stride))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight stride cells V x)
    (f : (K × I → ℤ) → ℝ)
    (hf : Integrable f (selectedResidueSmoothPMF stride cells V hV hZ).toMeasure) :
    selectedResidueDensityMass stride cells V f =
      ∫ x, f x ∂(selectedResidueSmoothPMF stride cells V hV hZ).toMeasure := by
  apply Complex.ofReal_injective
  rw [selectedResidueDensityMass_complex stride cells V hV hZ,
    ← integral_complex_ofReal, PMF.integral_eq_tsum _ _ hf.ofReal]
  simp only [Complex.real_smul]

end Erdos3

end

section

namespace Erdos3

theorem selectedResidueDensityPMF_zero_off {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D)
    (x : K × I → ℤ) (hx : x ∉ rectangularWeightIndices 0 V 1) :
    (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal = 0 := by
  rw [selectedResidueDensityPMF_toReal, selectedResidueSmoothPMF_toReal,
    selectedResidueSmoothWeight_zero_off modulus G V hV x hx]
  simp

theorem selectedResidueDensityPMF_zero_of_density_zero {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D)
    (x : K × I → ℤ) (hx : D x = 0) :
    (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal = 0 := by
  rw [selectedResidueDensityPMF_toReal, hx, mul_zero, zero_div]

theorem selectedResidueDensityPMF_domination {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D)
    (hlower : 1 / 2 ≤ selectedResidueDensityMass modulus G V D)
    {B : ℝ} (hbound : ∀ x, D x ≤ B) (x : K × I → ℤ) :
    (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal ≤
      2 * B * (selectedResidueSmoothPMF modulus G V hV hZ x).toReal := by
  rw [selectedResidueDensityPMF_toReal, mul_div_assoc]
  have hb := (normalized_weight_range D (fun y => ⟨hD0 y, hbound y⟩) hlower x).2
  have h := mul_le_mul_of_nonneg_left hb
    (ENNReal.toReal_nonneg : 0 ≤ (selectedResidueSmoothPMF modulus G V hV hZ x).toReal)
  simpa only [mul_comm] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def selectedResidueFiniteLaw {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x) :
    FiniteProbabilityWeights (rectangularWeightIndices 0 V 1) :=
  finiteSupportProbability (selectedResidueSmoothWeight modulus G V) (rectangularWeightIndices 0 V 1)
    (selectedResidueSmoothWeight_nonneg modulus G V)
    (selectedResidueSmoothWeight_zero_off modulus G V hV) hZ

theorem selectedResidueFiniteLaw_complexMean {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x) (f : (K × I → ℤ) → ℂ) :
    (selectedResidueFiniteLaw modulus G V hV hZ).complexMean (fun x => f x.val) =
      ∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * f x := by
  simp only [selectedResidueFiniteLaw, finiteSupportProbability_complexMean, selectedResidueSmoothPMF_toReal]

theorem selectedResidueFiniteLaw_mean {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x) (f : (K × I → ℤ) → ℝ) :
    (selectedResidueFiniteLaw modulus G V hV hZ).mean (fun x => f x.val) =
      ∑' x, (selectedResidueSmoothPMF modulus G V hV hZ x).toReal * f x := by
  apply Complex.ofReal_injective
  have h := selectedResidueFiniteLaw_complexMean modulus G V hV hZ (fun x => (f x : ℂ))
  rw [FiniteProbabilityWeights.complexMean_ofReal] at h
  simpa only [Complex.ofReal_tsum, Complex.ofReal_mul] using h

theorem selectedResidueFiniteLaw_densityMass {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x) (D : (K × I → ℤ) → ℝ) :
    (selectedResidueFiniteLaw modulus G V hV hZ).mean (fun x => D x.val) =
      selectedResidueDensityMass modulus G V D := by
  rw [selectedResidueFiniteLaw_mean]
  simp only [selectedResidueSmoothPMF_toReal, selectedResidueDensityMass, finiteDensityMass]

theorem selectedResidueDensityPMF_mean {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D) (f : (K × I → ℤ) → ℝ) :
    (∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal * f x) =
      (∑' x, (selectedResidueSmoothPMF modulus G V hV hZ x).toReal * (D x * f x)) /
        selectedResidueDensityMass modulus G V D := by
  simp only [selectedResidueDensityPMF_toReal, div_mul_eq_mul_div, mul_assoc, tsum_div_const]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

def columnResidueReduction {K I : Type*} (modulus refined : I → ℕ)
    (hdiv : ∀ i, modulus i ∣ refined i)
    (r : ColumnResiduePattern K I refined) : ColumnResiduePattern K I modulus :=
  fun z => ZMod.castHom (hdiv z.2) (ZMod (modulus z.2)) (r z)

@[simp] theorem columnResidueReduction_pattern {K I : Type*} (modulus refined : I → ℕ)
    (hdiv : ∀ i, modulus i ∣ refined i) (x : K × I → ℤ) :
    columnResidueReduction modulus refined hdiv (columnResiduePattern refined x) =
      columnResiduePattern modulus x := by
  funext z
  exact map_intCast (ZMod.castHom (hdiv z.2) (ZMod (modulus z.2))) (x z)

noncomputable def selectedResidueRefinement {K I : Type*} [Fintype K] [Fintype I]
    (modulus refined : I → ℕ) [∀ i, NeZero (refined i)]
    (hdiv : ∀ i, modulus i ∣ refined i) (G : Finset (ColumnResiduePattern K I modulus)) :
    Finset (ColumnResiduePattern K I refined) :=
  Finset.univ.filter (fun r => columnResidueReduction modulus refined hdiv r ∈ G)

@[simp] theorem mem_selectedResidueRefinement {K I : Type*} [Fintype K] [Fintype I]
    (modulus refined : I → ℕ) [∀ i, NeZero (refined i)]
    (hdiv : ∀ i, modulus i ∣ refined i) (G : Finset (ColumnResiduePattern K I modulus))
    (r : ColumnResiduePattern K I refined) :
    r ∈ selectedResidueRefinement modulus refined hdiv G ↔
      columnResidueReduction modulus refined hdiv r ∈ G := by
  simp only [selectedResidueRefinement, Finset.mem_filter, Finset.mem_univ, true_and]

theorem selectedResidueSmoothWeight_refinement {K I : Type*} [Fintype K] [Fintype I]
    (modulus refined : I → ℕ) [∀ i, NeZero (refined i)]
    (hdiv : ∀ i, modulus i ∣ refined i) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (x : K × I → ℤ) :
    selectedResidueSmoothWeight refined (selectedResidueRefinement modulus refined hdiv G) V x =
      selectedResidueSmoothWeight modulus G V x := by
  simp only [selectedResidueSmoothWeight, mem_selectedResidueRefinement,
    columnResidueReduction_pattern]

theorem selectedResidueSmoothMass_refinement {K I : Type*} [Fintype K] [Fintype I]
    (modulus refined : I → ℕ) [∀ i, NeZero (refined i)]
    (hdiv : ∀ i, modulus i ∣ refined i) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) :
    (∑' x, selectedResidueSmoothWeight refined (selectedResidueRefinement modulus refined hdiv G) V x) =
      ∑' x, selectedResidueSmoothWeight modulus G V x := by
  simp only [selectedResidueSmoothWeight_refinement]

theorem selectedResidueSmoothPMF_refinement {K I : Type*} [Fintype K] [Fintype I]
    (modulus refined : I → ℕ) [∀ i, NeZero (refined i)]
    (hdiv : ∀ i, modulus i ∣ refined i) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (hZ' : 0 < ∑' x, selectedResidueSmoothWeight refined
      (selectedResidueRefinement modulus refined hdiv G) V x) :
    selectedResidueSmoothPMF refined (selectedResidueRefinement modulus refined hdiv G) V hV hZ' =
      selectedResidueSmoothPMF modulus G V hV hZ := by
  ext x
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  simp only [selectedResidueSmoothPMF_toReal, selectedResidueSmoothWeight_refinement]

theorem selectedResidueRefinement_nonempty {K I : Type*} [Fintype K] [Fintype I]
    (modulus refined : I → ℕ) [∀ i, NeZero (refined i)]
    (hdiv : ∀ i, modulus i ∣ refined i) (G : Finset (ColumnResiduePattern K I modulus))
    (hG : G.Nonempty) : (selectedResidueRefinement modulus refined hdiv G).Nonempty := by
  obtain ⟨r, hr⟩ := hG
  refine ⟨columnResiduePattern refined (columnResidueRepresentative modulus r), ?_⟩
  rw [mem_selectedResidueRefinement, columnResidueReduction_pattern]
  have hrep : columnResiduePattern modulus (columnResidueRepresentative modulus r) = r := by
    funext z
    exact columnResidueRepresentative_cast modulus r z
  rwa [hrep]

noncomputable def selectedResidueExtraRefinement {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) [∀ i, NeZero (modulus i)] (q : ℕ) [NeZero q]
    (G : Finset (ColumnResiduePattern K I modulus)) :
    Finset (ColumnResiduePattern K I (fun i => modulus i * q)) :=
  selectedResidueRefinement modulus (fun i => modulus i * q) (fun i => dvd_mul_right (modulus i) q) G

def refinedColumnExtraResidue {K I : Type*} (modulus : I → ℕ) (q : ℕ)
    (r : ColumnResiduePattern K I (fun i => modulus i * q)) : K × I → ZMod q :=
  columnResidueReduction (fun _ => q) (fun i => modulus i * q)
    (fun i => dvd_mul_left q (modulus i)) r

theorem refinedColumnExtraResidue_of_pattern {K I : Type*} (modulus : I → ℕ) (q : ℕ)
    (r : ColumnResiduePattern K I (fun i => modulus i * q)) (x : K × I → ℤ)
    (hx : columnResiduePattern (fun i => modulus i * q) x = r) :
    (fun z => (x z : ZMod q)) = refinedColumnExtraResidue modulus q r := by
  rw [← hx, refinedColumnExtraResidue, columnResidueReduction_pattern]
  rfl

theorem refinedResidueLatticeArray_extraResidue {K I : Type*} (modulus : I → ℕ) (q : ℕ)
    (r : ColumnResiduePattern K I (fun i => modulus i * q)) (x : K × I → ℤ) :
    (fun z => (residueLatticeArray (columnResidueRepresentative (fun i => modulus i * q) r)
      (fun i => modulus i * q) x z : ZMod q)) = refinedColumnExtraResidue modulus q r := by
  apply refinedColumnExtraResidue_of_pattern
  funext z
  simp only [columnResiduePattern, residueLatticeArray, Int.cast_add, Int.cast_mul,
    Int.cast_natCast, ZMod.natCast_self, zero_mul, add_zero,
    columnResidueRepresentative_cast]

theorem selectedResidueDensityMass_refinement {K I : Type*} [Fintype K] [Fintype I]
    (modulus refined : I → ℕ) [∀ i, NeZero (refined i)]
    (hdiv : ∀ i, modulus i ∣ refined i) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (D : (K × I → ℤ) → ℝ) :
    selectedResidueDensityMass refined (selectedResidueRefinement modulus refined hdiv G) V D =
      selectedResidueDensityMass modulus G V D := by
  simp only [selectedResidueDensityMass, finiteDensityMass, selectedResidueSmoothWeight_refinement]

theorem selectedResidueDensityPMF_refinement {K I : Type*} [Fintype K] [Fintype I]
    (modulus refined : I → ℕ) [∀ i, NeZero (refined i)]
    (hdiv : ∀ i, modulus i ∣ refined i) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (hZ' : 0 < ∑' x, selectedResidueSmoothWeight refined
      (selectedResidueRefinement modulus refined hdiv G) V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D)
    (hD' : 0 < selectedResidueDensityMass refined
      (selectedResidueRefinement modulus refined hdiv G) V D) :
    selectedResidueDensityPMF refined (selectedResidueRefinement modulus refined hdiv G) V hV hZ'
        D hD0 hD' = selectedResidueDensityPMF modulus G V hV hZ D hD0 hD := by
  ext x
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  simp only [selectedResidueDensityPMF_toReal, selectedResidueDensityMass_refinement,
    selectedResidueSmoothPMF_toReal, selectedResidueSmoothWeight_refinement]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem selectedResidueDensityPMF_raw_error {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D)
    (f : (K × I → ℤ) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    {a : ℂ} {η γ : ℝ}
    (htest : ‖(∑' x, ((selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal : ℂ) * f x) - a‖ ≤ η)
    (hmass : |selectedResidueDensityMass modulus G V D - 1| ≤ γ) :
    ‖(∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * ((D x : ℂ) * f x)) - a‖ ≤ η + γ := by
  let p := selectedResidueDensityPMF modulus G V hV hZ D hD0 hD
  let b : ℂ := ∑' x, ((p x).toReal : ℂ) * f x
  have hb : ‖b‖ ≤ 1 := by
    have hh := pmf_complex_average_error p f (fun _ => 0) hf
      (fun _ => by simp : ∀ x, ‖(0 : ℂ)‖ ≤ (0 : ℝ)) (by simpa using hf)
    simpa only [mul_zero, tsum_zero, sub_zero, b] using hh
  have heq := selectedResidueDensityPMF_complexMean modulus G V hV hZ D hD0 hD f
  have hmassc : (selectedResidueDensityMass modulus G V D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hraw : (∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * ((D x : ℂ) * f x)) =
      (selectedResidueDensityMass modulus G V D : ℂ) * b := by
    dsimp only [b, p]
    rw [heq, mul_div_cancel₀ _ hmassc]
  rw [hraw]
  have hstep : ‖(selectedResidueDensityMass modulus G V D : ℂ) * b - b‖ ≤ γ := by
    rw [← sub_one_mul, norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left hb (abs_nonneg _)).trans (by simpa using hmass)
  have ht := norm_sub_le_norm_sub_add_norm_sub
    ((selectedResidueDensityMass modulus G V D : ℂ) * b) b a
  exact ht.trans (by linarith)

theorem selectedResidueDensityPMF_singleton_complexMean_congr {K I : Type*}
    [Fintype K] [Fintype I] (modulus : I → ℕ) (r : ColumnResiduePattern K I modulus)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus {r} V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus {r} V D)
    (f g : (K × I → ℤ) → ℂ)
    (heq : ∀ x, columnResiduePattern modulus x = r → f x = g x) :
    (∑' x, ((selectedResidueDensityPMF modulus {r} V hV hZ D hD0 hD x).toReal : ℂ) * f x) =
      ∑' x, ((selectedResidueDensityPMF modulus {r} V hV hZ D hD0 hD x).toReal : ℂ) * g x := by
  apply tsum_congr
  intro x
  by_cases hx : columnResiduePattern modulus x = r
  · rw [heq x hx]
  · have hz : (selectedResidueDensityPMF modulus {r} V hV hZ D hD0 hD x).toReal = 0 := by
      rw [selectedResidueDensityPMF_toReal, selectedResidueSmoothPMF_toReal]
      simp [selectedResidueSmoothWeight, hx]
    simp [hz]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem smoothProbabilityProfile_plateau (x : ℝ) (hx : |x| ≤ 1 / 2) :
    smoothProbabilityProfile x = smoothProbabilityProfile 0 := by
  have hx' : probabilityProfileBump x = 1 := probabilityProfileBump.one_of_mem_closedBall
    (by simpa [probabilityProfileBump, Real.dist_eq] using hx)
  have h0 : probabilityProfileBump 0 = 1 := probabilityProfileBump.one_of_mem_closedBall
    (by simp [probabilityProfileBump])
  simp only [smoothProbabilityProfile, ContDiffBump.normed_def, hx', h0]

theorem selectedResidueSmoothWeight_plateau {K X : Type*} [Fintype K] [Fintype X]
    (q : X → ℕ) (cells : Finset (ColumnResiduePattern K X q)) (V : K × X → ℝ)
    (z : K × X → ℤ) (hz : columnResiduePattern q z ∈ cells)
    (hsmall : ∀ i, |(z i : ℝ) / V i| ≤ 1 / 2) :
    selectedResidueSmoothWeight q cells V z =
      (smoothProbabilityProfile 0) ^ Fintype.card (K × X) := by
  classical
  simp only [selectedResidueSmoothWeight, hz, ite_true]
  unfold smoothProductProfile
  calc
    _ = ∏ _i : K × X, smoothProbabilityProfile 0 :=
      Finset.prod_congr rfl (fun i _ => smoothProbabilityProfile_plateau _ (hsmall i))
    _ = _ := by simp

theorem selectedResidueDensityMass_window_bound {K X : Type*} [Fintype K] [Fintype X]
    (q : X → ℕ) (cells : Finset (ColumnResiduePattern K X q))
    (V : K × X → ℝ) (hV : ∀ i, 0 < V i)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q cells V z)
    (D : (K × X → ℤ) → ℝ) (hD : ∀ z, 0 ≤ D z)
    (window : Finset (K × X → ℤ))
    (hresidue : ∀ z ∈ window, columnResiduePattern q z ∈ cells)
    (hsmall : ∀ z ∈ window, ∀ i, |(z i : ℝ) / V i| ≤ 1 / 2) :
    (∑ z ∈ window, D z) ≤
      ((∑' z, selectedResidueSmoothWeight q cells V z) /
        (smoothProbabilityProfile 0) ^ Fintype.card (K × X)) *
          selectedResidueDensityMass q cells V D := by
  apply finiteDensityMass_sum_le_of_weight_lower (selectedResidueSmoothWeight q cells V) D
    (rectangularWeightIndices 0 V 1) window (selectedResidueSmoothWeight_nonneg q cells V)
    (selectedResidueSmoothWeight_zero_off q cells V hV) hD hZ
    (pow_pos smoothProbabilityProfile_pos_zero _)
  intro z hz
  exact (selectedResidueSmoothWeight_plateau q cells V z (hresidue z hz) (hsmall z hz)).ge

theorem selectedResidueSmoothWeight_singleton_mass_upper {K X : Type*} [Fintype K] [Fintype X]
    (q : X → ℕ) (hq : ∀ x, 0 < q x) (r : ColumnResiduePattern K X q)
    (V : K × X → ℝ) (hV : ∀ i, 0 < V i)
    (hscale : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth q V i) :
    (∑' z, selectedResidueSmoothWeight q {r} V z) ≤
      (3 / 2 : ℝ) ^ Fintype.card (K × X) * ∏ i, residueProfileWidth q V i := by
  classical
  have he : selectedResidueSmoothWeight q {r} V =
      residueSmoothWeight (columnResidueRepresentative q r) q V := by
    funext z
    simp only [selectedResidueSmoothWeight, residueSmoothWeight_eq_pattern, Finset.mem_singleton]
  rw [he, ← residueSmoothWeight_mass _ q hq V hV,
    shiftedSmoothProductMass_eq_prod _ _ (residueProfileWidth_pos q V hq hV)]
  calc
    _ ≤ ∏ i : K × X, 3 * residueProfileWidth q V i / 2 := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact tsum_nonneg (fun _ => (smoothProbabilityProfile_range _).1)
      · intro i _
        exact (shiftedSmoothSampleSum_bounds _ (hscale i)).2
    _ = _ := by
      simp_rw [show ∀ i : K × X, 3 * residueProfileWidth q V i / 2 =
        (3 / 2 : ℝ) * residueProfileWidth q V i by intro i; ring]
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ]

theorem selectedResidueDensityMass_singleton_window_bound {K X : Type*} [Fintype K] [Fintype X]
    (q : X → ℕ) (hq : ∀ x, 0 < q x) (r : ColumnResiduePattern K X q)
    (V : K × X → ℝ) (hV : ∀ i, 0 < V i)
    (hscale : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth q V i)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q {r} V z)
    (D : (K × X → ℤ) → ℝ) (hD : ∀ z, 0 ≤ D z)
    (window : Finset (K × X → ℤ))
    (hresidue : ∀ z ∈ window, columnResiduePattern q z = r)
    (hsmall : ∀ z ∈ window, ∀ i, |(z i : ℝ) / V i| ≤ 1 / 2) :
    (∑ z ∈ window, D z) ≤
      ((3 / 2 : ℝ) ^ Fintype.card (K × X) * (∏ i, residueProfileWidth q V i) /
        (smoothProbabilityProfile 0) ^ Fintype.card (K × X)) *
          selectedResidueDensityMass q {r} V D := by
  classical
  have hm : 0 ≤ selectedResidueDensityMass q {r} V D := by
    apply tsum_nonneg
    intro z
    exact mul_nonneg (div_nonneg (selectedResidueSmoothWeight_nonneg q {r} V z) hZ.le) (hD z)
  apply (selectedResidueDensityMass_window_bound q {r} V hV hZ D hD window
    (fun z hz => Finset.mem_singleton.mpr (hresidue z hz)) hsmall).trans
  apply mul_le_mul_of_nonneg_right _ hm
  exact div_le_div_of_nonneg_right (selectedResidueSmoothWeight_singleton_mass_upper q hq r V hV hscale)
    (pow_pos smoothProbabilityProfile_pos_zero _).le

end Erdos3

end

end OAI
