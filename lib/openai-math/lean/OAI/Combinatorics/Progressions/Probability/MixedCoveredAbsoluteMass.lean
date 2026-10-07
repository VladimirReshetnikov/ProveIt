import OAI.Combinatorics.Progressions.Estimates.AllocatedCoveredSiteExpansion

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical

variable {m : ℕ} {I O J E : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
variable (hΩm : ∀ j t, MeasurableSet (Ω j t))
variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d Ω
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))
local notation "raw" => mixedCoveredJetRawReference (I := I) (O := O) (E := E) (n := n) d

include hΩm hΩ

theorem mixedCoveredJet_normalized_lintegral_abs
    (f : MixedCoveredJetSource I O E n d → ℝ) :
    (∫⁻ y, ENNReal.ofReal |restrictedChartDensity chart region 1
      (fun z => f z / coveredJetArrayScale (O := O) U) y| ∂haar) =
      ∫⁻ z in region, ENNReal.ofReal |f z| ∂raw := by
  have ha := restrictedChartDensity_abs chart region
    (mixedCoveredJetChart_injOn U o b hb bW d Ω hΩ)
    (fun z => f z / coveredJetArrayScale (O := O) U)
  simp_rw [abs_div, abs_of_pos (coveredJetArrayScale_pos U)] at ha
  calc
    _ = ∫⁻ y, ENNReal.ofReal (restrictedChartDensity chart region 1
        (fun z => |f z| / coveredJetArrayScale (O := O) U) y) ∂haar :=
      lintegral_congr (fun y => congrArg ENNReal.ofReal (congrFun ha y))
    _ = _ := mixedCoveredJet_normalized_lintegral U o b hb bW d ν Ω hΩm hΩ (fun z => |f z|)

theorem mixedCoveredJet_normalized_lintegral_abs_le
    (f : MixedCoveredJetSource I O E n d → ℝ) :
    (∫⁻ y, ENNReal.ofReal |restrictedChartDensity chart region 1
      (fun z => f z / coveredJetArrayScale (O := O) U) y| ∂haar) ≤
      ∫⁻ z, ENNReal.ofReal |f z| ∂raw := by
  rw [mixedCoveredJet_normalized_lintegral_abs U o b hb bW d ν Ω hΩm hΩ]
  exact lintegral_mono' Measure.restrict_le_self le_rfl

theorem mixedCoveredJet_normalized_integrable
    (f : MixedCoveredJetSource I O E n d → ℝ) (hfm : Measurable f) (hfi : Integrable f raw) :
    Integrable (restrictedChartDensity chart region 1
      (fun z => f z / coveredJetArrayScale (O := O) U)) haar := by
  refine ⟨(mixedCoveredJet_restrictedDensity_measurable U o b hb bW d Ω hΩm hΩ _
    (hfm.div_const _)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  have hf : (∫⁻ z, ENNReal.ofReal |f z| ∂raw) < ⊤ := by
    simpa only [Real.norm_eq_abs] using ((hasFiniteIntegral_iff_norm f).mp hfi.hasFiniteIntegral)
  simpa only [Real.norm_eq_abs] using
    (mixedCoveredJet_normalized_lintegral_abs_le U o b hb bW d ν Ω hΩm hΩ f).trans_lt hf

theorem mixedCoveredJet_normalized_integral_abs_le
    (f : MixedCoveredJetSource I O E n d → ℝ) (hfm : Measurable f) (hfi : Integrable f raw) :
    (∫ y, |restrictedChartDensity chart region 1
      (fun z => f z / coveredJetArrayScale (O := O) U) y| ∂haar) ≤ ∫ z, |f z| ∂raw := by
  have hi := mixedCoveredJet_normalized_integrable U o b hb bW d ν Ω hΩm hΩ f hfm hfi
  have he := mixedCoveredJet_normalized_lintegral_abs_le U o b hb bW d ν Ω hΩm hΩ f
  rw [← ofReal_integral_eq_lintegral_ofReal hi.abs (ae_of_all _ (fun _ => abs_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal hfi.abs (ae_of_all _ (fun _ => abs_nonneg _))] at he
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun _ => abs_nonneg _))).mp he

end Erdos3.VectorPolynomial

end

end OAI
