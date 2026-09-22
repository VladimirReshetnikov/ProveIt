import Surreal.Foundations.SignSequenceMonomialAlgebra
import Surreal.Foundations.SignSequenceFiniteLeading
import Mathlib.RingTheory.HahnSeries.Lex

/-!
# Faithful finite normal forms in the sign field

For strictly increasing additive exponent maps, finite monomial evaluation
is injective and has exactly the leading coefficient, valuation, and order
of the associated finitely supported Hahn series. This proves the finite
normal-form case of the arithmetic comparison required by
`found:eq:normalform`. Infinite supports remain a separate construction.
-/

universe u v

namespace Surreal.Foundations.SignSequence

noncomputable section

variable {Γ : Type v} [AddMonoid Γ] [LinearOrder Γ]

/-- The least nonzero exponent of a finite coefficient family gives its
actual surreal valuation and leading real coefficient. -/
theorem finiteMonomialEvaluation_leading (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (F : AddMonoidAlgebra ℝ Γ) (j : Γ) (hj : j ∈ F.coeff.support)
    (hmin : ∀ i ∈ F.coeff.support, j ≤ i) :
    valuation (finiteMonomialEvaluation e F) = (e j : WithTop SignSequence.{u}) ∧
      leadingCoeff (finiteMonomialEvaluation e F) = F.coeff j := by
  classical
  rw [finiteMonomialEvaluation_eq_sum]
  apply leading_finite_monomial_sum F.coeff.support e F.coeff j hj
    (Finsupp.mem_support_iff.mp hj)
  intro i hi hij
  exact he (lt_of_le_of_ne (hmin i hi) (Ne.symm hij))

/-- No nonempty finite normal form can evaluate to zero. -/
theorem finiteMonomialEvaluation_ne_zero (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    {F : AddMonoidAlgebra ℝ Γ} (hF : F ≠ 0) : finiteMonomialEvaluation e F ≠ 0 := by
  classical
  have hs : F.coeff.support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr (AddMonoidAlgebra.coeff_eq_zero.not.mpr hF)
  let j := F.coeff.support.min' hs
  have hj : j ∈ F.coeff.support := Finset.min'_mem _ _
  have hlead := (finiteMonomialEvaluation_leading e he F j hj
    (fun _ hi => Finset.min'_le _ _ hi)).1
  intro hzero
  rw [hzero, valuation_zero] at hlead
  exact WithTop.top_ne_coe hlead

/-- Finite normal forms with distinct ordered exponents are unique in the
actual sign field, with no infinite summation assumption. -/
theorem finiteMonomialEvaluation_injective (e : Γ →+ SignSequence.{u}) (he : StrictMono e) :
    Function.Injective (finiteMonomialEvaluation e) := by
  intro F G h
  have hz : finiteMonomialEvaluation e (F - G) = 0 := by
    rw [map_sub, h, _root_.sub_self]
  have hFG : F - G = 0 := by
    by_contra hFG
    exact finiteMonomialEvaluation_ne_zero e he hFG hz
  exact sub_eq_zero.mp hFG

/-- The leading real coefficient agrees with that of the finite Hahn series
on exactly the same coefficient data. -/
theorem leadingCoeff_finiteMonomialEvaluation (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (F : AddMonoidAlgebra ℝ Γ) :
    leadingCoeff (finiteMonomialEvaluation e F) =
      (_root_.HahnSeries.ofFinsupp F.coeff).leadingCoeff := by
  classical
  by_cases hF : F = 0
  · simp [hF]
  have hs : F.coeff.support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr (AddMonoidAlgebra.coeff_eq_zero.not.mpr hF)
  let j := F.coeff.support.min' hs
  have hj : j ∈ F.coeff.support := Finset.min'_mem _ _
  have hmin : ∀ i ∈ F.coeff.support, j ≤ i := fun _ hi => Finset.min'_le _ _ hi
  have ho : (_root_.HahnSeries.ofFinsupp F.coeff).orderTop = (j : WithTop Γ) :=
    _root_.HahnSeries.orderTop_eq_of_le (Finsupp.mem_support_iff.mp hj)
      (fun _ hi => hmin _ (Finsupp.mem_support_iff.mpr hi))
  rw [(finiteMonomialEvaluation_leading e he F j hj hmin).2,
    _root_.HahnSeries.leadingCoeff, ho]
  rfl

/-- The valuation agrees with the finite Hahn order under the given exponent
embedding, including the value infinity at the zero polynomial. -/
theorem valuation_finiteMonomialEvaluation (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (F : AddMonoidAlgebra ℝ Γ) :
    valuation (finiteMonomialEvaluation e F) =
      WithTop.map e (_root_.HahnSeries.ofFinsupp F.coeff).orderTop := by
  classical
  by_cases hF : F = 0
  · simp [hF]
  have hs : F.coeff.support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr (AddMonoidAlgebra.coeff_eq_zero.not.mpr hF)
  let j := F.coeff.support.min' hs
  have hj : j ∈ F.coeff.support := Finset.min'_mem _ _
  have hmin : ∀ i ∈ F.coeff.support, j ≤ i := fun _ hi => Finset.min'_le _ _ hi
  have ho : (_root_.HahnSeries.ofFinsupp F.coeff).orderTop = (j : WithTop Γ) :=
    _root_.HahnSeries.orderTop_eq_of_le (Finsupp.mem_support_iff.mp hj)
      (fun _ hi => hmin _ (Finsupp.mem_support_iff.mpr hi))
  rw [(finiteMonomialEvaluation_leading e he F j hj hmin).1, ho, WithTop.map_coe]

/-- Positivity of a finite Hahn normal form is exactly positivity of its
evaluation in the actual sign field. -/
theorem finiteMonomialEvaluation_pos_iff (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (F : AddMonoidAlgebra ℝ Γ) :
    0 < finiteMonomialEvaluation e F ↔ 0 < toLex (_root_.HahnSeries.ofFinsupp F.coeff) := by
  rw [← leadingCoeff_pos_iff, leadingCoeff_finiteMonomialEvaluation e he]
  exact _root_.HahnSeries.leadingCoeff_pos_iff

end

end Surreal.Foundations.SignSequence
