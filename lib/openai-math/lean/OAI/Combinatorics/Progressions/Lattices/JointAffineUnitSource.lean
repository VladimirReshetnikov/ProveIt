/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Estimates.SelectedSplitUnitSource

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def affineJetUnitMap {Z X K α I J N : Type*}
    [Fintype α] [DecidableEq α] [Fintype I] [Fintype J] [Fintype N]
    (s : I ↪ J) (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (F : (UnselectedColumn s → ℝ) →L[ℝ] (I → ℝ))
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℝ)
    (rows : I → Finset α) (c w : J ⊕ N → ℝ) (x : X → ℝ) (r : J ⊕ N → ℝ) : I → ℝ :=
  A (fun i => c (.inl (s i))+w (.inl (s i))*r (.inl (s i))) +
    F (fun j => c (.inl j.val)+w (.inl j.val)*r (.inl j.val)) +
      polynomialColumns (fun o n => normalizedJetColumn (e n) input z (rows o)) x
        (fun n => c (.inr n)+w (.inr n)*r (.inr n))

theorem affineJetUnitMap_measurable_comp {Ω Z X K α I J N : Type*} [MeasurableSpace Ω]
    [Fintype α] [DecidableEq α] [Fintype I] [Fintype J] [Fintype N]
    (s : I ↪ J) (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (F : (UnselectedColumn s → ℝ) →L[ℝ] (I → ℝ))
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (rows : I → Finset α)
    (c w r : Ω → J ⊕ N → ℝ) (hc : Measurable c) (hw : Measurable w) (hr : Measurable r)
    (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun a => z a j))
    (x : Ω → X → ℝ) (hx : ∀ j, Measurable (fun a => x a j)) :
    Measurable (fun a => affineJetUnitMap s A F e input (z a) rows (c a) (w a) (x a) (r a)) := by
  have htail := normalizedJetColumns_measurable_comp e input rows z hz x hx
    (fun a n => c a (.inr n)+w a (.inr n)*r a (.inr n)) (fun _ => by fun_prop)
  have hker : Measurable (fun a =>
      A (fun i => c a (.inl (s i))+w a (.inl (s i))*r a (.inl (s i))) +
        F (fun j => c a (.inl j.val)+w a (.inl j.val)*r a (.inl j.val))) := by fun_prop
  exact hker.add htail

theorem affineSelectedJetDensity_unit_law {Z X K α I J N : Type*}
    [Fintype α] [DecidableEq α] [Fintype I] [Fintype J] [Fintype N]
    (s : I ↪ J) (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (F : (UnselectedColumn s → ℝ) →L[ℝ] (I → ℝ))
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℝ)
    (rows : I → Finset α) (c w : J ⊕ N → ℝ) (hw : ∀ j, 0 < w j)
    (R : ℝ≥0) (hsupport : ∀ j, |c j|+w j ≤ R) (x : X → ℝ) :
    (realDensityMeasure volume (smoothProductProfile (J ⊕ N))).map
      (affineJetUnitMap s A F e input z rows c w x) =
      realDensityMeasure volume (affineSelectedJetDensity s A F e input z rows c w x) := by
  let C := polynomialColumns (fun o n => normalizedJetColumn (e n) input z (rows o)) x
  let H := fun p : (UnselectedColumn s ⊕ N → ℝ) × (I → ℝ) => A p.2+splitFreeColumns F C p.1
  have hH : Measurable H := by fun_prop
  have he : affineJetUnitMap s A F e input z rows c w x =
      H ∘ (fun r => (selectedSplitMeasurableEquiv s).symm (fun j => c j+w j*r j)) := by
    funext r
    simp only [Function.comp_def, selectedSplitMeasurableEquiv_symm_apply,
      H, splitFreeColumns_apply, affineJetUnitMap, add_assoc, C, Sum.elim_inl, Sum.elim_inr]
  have hinput : Measurable (fun r : J ⊕ N → ℝ =>
      (selectedSplitMeasurableEquiv s).symm (fun j => c j+w j*r j)) :=
    (selectedSplitMeasurableEquiv s).symm.measurable.comp (by fun_prop)
  rw [he, ← Measure.map_map hH hinput, selectedSplit_unit_law s c w hw]
  have hp := affineSelectedJetProfile_probability_data s c w hw R hsupport
  exact pivotOutputDensity_law A (splitFreeColumns F C) hp.1 hp.2.1

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

noncomputable def jointUnitCoefficientSource {Q : Type*} [Fintype Q]
    (J N : Q → Type*) [∀ q, Fintype (J q)] [∀ q, Fintype (N q)] :
    Measure (∀ q, J q ⊕ N q → ℝ) := Measure.pi (fun q => unitCoefficientSource (J q ⊕ N q))

instance jointUnitCoefficientSource_probability {Q : Type*} [Fintype Q]
    (J N : Q → Type*) [∀ q, Fintype (J q)] [∀ q, Fintype (N q)] :
    IsProbabilityMeasure (jointUnitCoefficientSource J N) := by
  unfold jointUnitCoefficientSource
  infer_instance

noncomputable def jointAffineJetUnitMap {Q Z X K α : Type*}
    [Fintype Q] [Fintype α] [DecidableEq α] {I J N : Q → Type*}
    [∀ q, Fintype (I q)] [∀ q, Fintype (J q)] [∀ q, Fintype (N q)]
    (s : ∀ q, I q ↪ J q) (A : ∀ q, (I q → ℝ) ≃L[ℝ] (I q → ℝ))
    (F : ∀ q, (UnselectedColumn (s q) → ℝ) →L[ℝ] (I q → ℝ))
    (e : ∀ q, N q → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℝ)
    (rows : ∀ q, I q → Finset α) (c w : ∀ q, J q ⊕ N q → ℝ)
    (x : X → ℝ) (r : ∀ q, J q ⊕ N q → ℝ) : ∀ q, I q → ℝ :=
  fun q => affineJetUnitMap (s q) (A q) (F q) (e q) input z (rows q) (c q) (w q) x (r q)

theorem jointAffineJetUnitMap_measurable_comp {Ω Q Z X K α : Type*} [MeasurableSpace Ω]
    [Fintype Q] [Fintype α] [DecidableEq α] {I J N : Q → Type*}
    [∀ q, Fintype (I q)] [∀ q, Fintype (J q)] [∀ q, Fintype (N q)]
    (s : ∀ q, I q ↪ J q) (A : ∀ q, (I q → ℝ) ≃L[ℝ] (I q → ℝ))
    (F : ∀ q, (UnselectedColumn (s q) → ℝ) →L[ℝ] (I q → ℝ))
    (e : ∀ q, N q → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (rows : ∀ q, I q → Finset α)
    (c w r : Ω → ∀ q, J q ⊕ N q → ℝ)
    (hc : ∀ q, Measurable (fun a => c a q)) (hw : ∀ q, Measurable (fun a => w a q))
    (hr : ∀ q, Measurable (fun a => r a q))
    (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun a => z a j))
    (x : Ω → X → ℝ) (hx : ∀ j, Measurable (fun a => x a j)) :
    Measurable (fun a => jointAffineJetUnitMap s A F e input (z a) rows (c a) (w a) (x a) (r a)) := by
  apply Measurable.of_eval
  intro q
  exact affineJetUnitMap_measurable_comp (s q) (A q) (F q) (e q) input (rows q)
    (fun a => c a q) (fun a => w a q) (fun a => r a q) (hc q) (hw q) (hr q) z hz x hx

theorem jointAffineJetDensity_unit_law {Q Z X K α : Type*}
    [Fintype Q] [Fintype α] [DecidableEq α] {I J N : Q → Type*}
    [∀ q, Fintype (I q)] [∀ q, Fintype (J q)] [∀ q, Fintype (N q)]
    (s : ∀ q, I q ↪ J q) (A : ∀ q, (I q → ℝ) ≃L[ℝ] (I q → ℝ))
    (F : ∀ q, (UnselectedColumn (s q) → ℝ) →L[ℝ] (I q → ℝ))
    (e : ∀ q, N q → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℝ)
    (rows : ∀ q, I q → Finset α) (c w : ∀ q, J q ⊕ N q → ℝ) (hw : ∀ q j, 0 < w q j)
    (R : Q → ℝ≥0) (hsupport : ∀ q j, |c q j|+w q j ≤ R q) (x : X → ℝ) :
    (jointUnitCoefficientSource J N).map (jointAffineJetUnitMap s A F e input z rows c w x) =
      realDensityMeasure volume (jointAffineJetDensity s A F e input z rows c w x) := by
  have hm (q) : Measurable (affineJetUnitMap (s q) (A q) (F q) (e q) input z (rows q) (c q) (w q) x) :=
    affineJetUnitMap_measurable_comp (s q) (A q) (F q) (e q) input (rows q)
      (fun _ => c q) (fun _ => w q) id measurable_const measurable_const measurable_id
      (fun _ => z) (fun _ => measurable_const) (fun _ => x) (fun _ => measurable_const)
  unfold jointUnitCoefficientSource jointAffineJetUnitMap
  rw [Measure.pi_map_pi (fun q => (hm q).aemeasurable)]
  have hlaw (q) := affineSelectedJetDensity_unit_law (s q) (A q) (F q) (e q) input z
    (rows q) (c q) (w q) (hw q) (R q) (hsupport q) x
  change (Measure.pi (fun q => (realDensityMeasure volume (smoothProductProfile (J q ⊕ N q))).map _)) = _
  simp_rw [hlaw]
  have hp (q) := affineSelectedJetProfile_probability_data (s q) (c q) (w q) (hw q) (R q) (hsupport q)
  exact realDensityMeasure_pi (fun _ => volume) _
    (fun q => pivotOutputDensity_integrable (A q) _ (hp q).1)
    (fun q => pivotOutputDensity_nonneg (A q) _ (hp q).2.1)

end Erdos3

end

end OAI
