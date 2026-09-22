import Surreal.Foundations.SignSequenceStrongAlgebra
import Surreal.Surcomplex.StrongSummation
import Surreal.Surcomplex.ComplexEmbedding
import Surreal.HahnSeries.Constants

/-!
# Strong sums of actual ordinary constants

A real or complex constant family is strongly summable exactly when only
finitely many members are nonzero. Its strong sum is the embedded finite
coefficient sum. In particular the ordinary convergent geometric family
with coefficients `2⁻ⁿ` is not an actual Hahn strong sum, as required by
`a:rule:clauseii`, `a:ex:notsummable`, and `found:ex:failed`.
-/

universe u v

namespace Surreal

open Foundations

noncomputable section

namespace Foundations.SignSequence

/-- An ordinary real has exactly its constant canonical Hahn series. -/
@[simp] theorem rawNormalForm_ofReal (r : ℝ) :
    rawNormalForm (ofReal r : SignSequence.{u}) = _root_.HahnSeries.single 0 r := by
  rw [rawNormalForm, SmallNormalForm.normalForm_ofReal]
  apply _root_.HahnSeries.ext
  funext a
  change (_root_.SurrealHahnSeries.single (toSurreal 0) r).coeff (OrderDual.ofDual a) = _
  simp [toSurreal_zero, _root_.SurrealHahnSeries.coeff_single, Pi.single_apply,
    _root_.HahnSeries.coeff_single]

/-- The finite coefficient-fiber condition is necessary and sufficient for real constants. -/
theorem stronglySummable_ofReal_iff {ι : Type v} (c : ι → ℝ) :
    StronglySummable (fun i => (ofReal (c i) : SignSequence.{u})) ↔ c.HasFiniteSupport := by
  rw [← Surreal.HahnSeries.summable_constants_iff (Γ := _root_.Surreal.{u}ᵒᵈ) c]
  constructor
  · intro h
    exact ⟨h.toHahnFamily, fun i => rawNormalForm_ofReal (c i)⟩
  · rintro ⟨s, hs⟩
    exact stronglySummable_of_hahnFamily s (fun i => (hs i).trans (rawNormalForm_ofReal (c i)).symm)

/-- The actual sum of a strongly summable constant real family is its finite real sum. -/
theorem strongSum_ofReal {ι : Type v} [Small.{u} ι] (c : ι → ℝ)
    (hc : StronglySummable (fun i => (ofReal (c i) : SignSequence.{u}))) :
    strongSum (fun i => ofReal (c i)) hc = ofReal (∑ᶠ i, c i) := by
  apply rawNormalForm_injective
  rw [rawNormalForm_strongSum, rawNormalForm_ofReal]
  exact Surreal.HahnSeries.hsum_constants c hc.toHahnFamily
    (fun i => rawNormalForm_ofReal (c i))

/-- Infinitely many nonzero ordinary real constants cannot form a strong sum. -/
theorem not_stronglySummable_ofReal {ι : Type v} [Infinite ι]
    (c : ι → ℝ) (hc : ∀ i, c i ≠ 0) :
    ¬ StronglySummable (fun i => (ofReal (c i) : SignSequence.{u})) := by
  intro h
  have hs := (stronglySummable_ofReal_iff c).mp h
  exact Set.infinite_univ (hs.subset fun i _ => hc i)

end Foundations.SignSequence

namespace Surcomplex

/-- An ordinary complex constant has exactly its constant canonical Hahn series. -/
@[simp] theorem rawNormalForm_ofComplex (c : ℂ) :
    rawNormalForm (ofComplex c : Surcomplex.{u}) = _root_.HahnSeries.single 0 c := by
  apply _root_.HahnSeries.ext
  funext a
  rw [coeff_rawNormalForm, ofComplex_re, ofComplex_im,
    SignSequence.rawNormalForm_ofReal, SignSequence.rawNormalForm_ofReal]
  by_cases ha : a = 0
  · subst a
    simp only [_root_.HahnSeries.coeff_single_same]
  · simp only [_root_.HahnSeries.coeff_single_of_ne ha]
    rfl

/-- Actual complex constants are strongly summable exactly when finitely many are nonzero. -/
theorem stronglySummable_ofComplex_iff {ι : Type v} (c : ι → ℂ) :
    StronglySummable (fun i => (ofComplex (c i) : Surcomplex.{u})) ↔ c.HasFiniteSupport := by
  rw [← Surreal.HahnSeries.summable_constants_iff (Γ := _root_.Surreal.{u}ᵒᵈ) c]
  constructor
  · intro h
    exact ⟨h.toHahnFamily, fun i => rawNormalForm_ofComplex (c i)⟩
  · rintro ⟨s, hs⟩
    constructor
    · simpa only [hs, rawNormalForm_ofComplex] using s.isPWO_iUnion_support
    · intro a
      simpa only [hs, rawNormalForm_ofComplex, Function.HasFiniteSupport, Function.support]
        using s.finite_co_support a

/-- The constant complex strong sum is the embedded finite coefficient sum. -/
theorem strongSum_ofComplex {ι : Type v} [Small.{u} ι] (c : ι → ℂ)
    (hc : StronglySummable (fun i => (ofComplex (c i) : Surcomplex.{u}))) :
    strongSum (fun i => ofComplex (c i)) hc = ofComplex (∑ᶠ i, c i) := by
  apply rawNormalForm_injective
  rw [rawNormalForm_strongSum, rawNormalForm_ofComplex]
  exact Surreal.HahnSeries.hsum_constants c hc.toHahnFamily
    (fun i => rawNormalForm_ofComplex (c i))

/-- The obstruction is infinite coefficient incidence, despite singleton supports. -/
theorem not_stronglySummable_ofComplex {ι : Type v} [Infinite ι]
    (c : ι → ℂ) (hc : ∀ i, c i ≠ 0) :
    ¬ StronglySummable (fun i => (ofComplex (c i) : Surcomplex.{u})) := by
  intro h
  have hs := (stronglySummable_ofComplex_iff c).mp h
  exact Set.infinite_univ (hs.subset fun i _ => hc i)

/-- The constant geometric family in `a:ex:notsummable` fails strong summability. -/
theorem not_stronglySummable_geometric_constants :
    ¬ StronglySummable (fun n : ℕ => (ofComplex (((2 : ℂ)⁻¹) ^ n) : Surcomplex.{u})) :=
  not_stronglySummable_ofComplex _
    (fun n => pow_ne_zero n (inv_ne_zero (two_ne_zero : (2 : ℂ) ≠ 0)))

end Surcomplex

end

end Surreal
