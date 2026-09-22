import Surreal.Surcomplex.FiniteLeading
import Surreal.HahnSeries.FiniteSupport
import Mathlib.Algebra.MonoidAlgebra.Lift

/-!
# Faithful finite normal forms in the actual surcomplex field

Finite complex coefficient expressions evaluate by a ring homomorphism in
the actual surcomplex field. A strictly increasing additive exponent map
preserves the least-support valuation and complex leading coefficient, and
makes this evaluation injective.
These are finite-support clauses of `found:eq:normalform` and
`found:thm:workspace`; infinite Hahn evaluation is a separate obligation.
-/

universe u v

namespace Surreal.Surcomplex

open Foundations

noncomputable section

variable {Γ : Type v} [AddMonoid Γ]

/-- The actual real-axis monomials form a multiplicative character. -/
def monomialMap (e : Γ →+ SignSequence.{u}) : Multiplicative Γ →* Surcomplex.{u} where
  toFun g := tMonomial (e g.toAdd)
  map_one' := by simp
  map_mul' a b := by
    change tMonomial (e (a.toAdd + b.toAdd)) = tMonomial (e a.toAdd) * tMonomial (e b.toAdd)
    rw [map_add, tMonomial_add]

/-- Evaluate finite complex normal forms in the constructed surcomplex field. -/
def finiteMonomialEvaluation (e : Γ →+ SignSequence.{u}) :
    AddMonoidAlgebra ℂ Γ →+* Surcomplex.{u} :=
  AddMonoidAlgebra.liftNCRingHom ofComplex (monomialMap e) (fun _ _ => Commute.all _ _)

@[simp] theorem finiteMonomialEvaluation_single (e : Γ →+ SignSequence.{u}) (g : Γ) (c : ℂ) :
    finiteMonomialEvaluation e (AddMonoidAlgebra.single g c) = ofComplex c * tMonomial (e g) :=
  AddMonoidAlgebra.liftNCRingHom_single _ _ _ _ _

/-- Evaluation is the displayed finite coefficient sum. -/
theorem finiteMonomialEvaluation_eq_sum (e : Γ →+ SignSequence.{u}) (F : AddMonoidAlgebra ℂ Γ) :
    finiteMonomialEvaluation e F =
      ∑ g ∈ F.coeff.support, ofComplex (F.coeff g) * tMonomial (e g) := by
  calc
    finiteMonomialEvaluation e F =
        finiteMonomialEvaluation e (F.coeff.sum AddMonoidAlgebra.single) := by
      rw [AddMonoidAlgebra.sum_coeff_single]
    _ = _ := by simp only [Finsupp.sum, map_sum, finiteMonomialEvaluation_single]

/-- A nonzero complex coefficient does not change a monomial's valuation. -/
theorem valuation_complex_mul_tMonomial {c : ℂ} (hc : c ≠ 0) (a : SignSequence.{u}) :
    valuation (ofComplex c * tMonomial a) = (a : WithTop SignSequence.{u}) := by
  rw [valuation_mul, valuation_ofComplex hc, valuation_tMonomial, zero_add]

variable [LinearOrder Γ]

/-- The least nonzero exponent gives the actual complex leading coefficient
as well as the valuation. -/
theorem finiteMonomialEvaluation_leading (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (F : AddMonoidAlgebra ℂ Γ) (j : Γ) (hj : j ∈ F.coeff.support)
    (hmin : ∀ i ∈ F.coeff.support, j ≤ i) :
    valuation (finiteMonomialEvaluation e F) = (e j : WithTop SignSequence.{u}) ∧
      leadingCoeff (finiteMonomialEvaluation e F) = F.coeff j := by
  classical
  rw [finiteMonomialEvaluation_eq_sum]
  apply leading_finite_monomial_sum F.coeff.support e F.coeff j hj
    (Finsupp.mem_support_iff.mp hj)
  intro i hi hij
  exact he (lt_of_le_of_ne (hmin i hi) (Ne.symm hij))

/-- The least nonzero coefficient determines the actual valuation. -/
theorem finiteMonomialEvaluation_valuation (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (F : AddMonoidAlgebra ℂ Γ) (j : Γ) (hj : j ∈ F.coeff.support)
    (hmin : ∀ i ∈ F.coeff.support, j ≤ i) :
    valuation (finiteMonomialEvaluation e F) = (e j : WithTop SignSequence.{u}) := by
  classical
  rw [finiteMonomialEvaluation_eq_sum]
  rw [← valuation_complex_mul_tMonomial (Finsupp.mem_support_iff.mp hj) (e j)]
  apply (AddValuation.toValuation valuation).map_sum_eq_of_lt hj
  intro i hi
  obtain ⟨his, hij⟩ := Finset.mem_sdiff.mp hi
  change valuation (ofComplex (F.coeff j) * tMonomial (e j)) <
    valuation (ofComplex (F.coeff i) * tMonomial (e i))
  rw [valuation_complex_mul_tMonomial (Finsupp.mem_support_iff.mp hj),
    valuation_complex_mul_tMonomial (Finsupp.mem_support_iff.mp his)]
  apply WithTop.coe_lt_coe.mpr
  apply he
  exact lt_of_le_of_ne (hmin i his)
    (Ne.symm (by simpa only [Finset.mem_singleton] using hij))

theorem finiteMonomialEvaluation_ne_zero (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    {F : AddMonoidAlgebra ℂ Γ} (hF : F ≠ 0) : finiteMonomialEvaluation e F ≠ 0 := by
  classical
  have hs : F.coeff.support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr (AddMonoidAlgebra.coeff_eq_zero.not.mpr hF)
  let j := F.coeff.support.min' hs
  have hv := finiteMonomialEvaluation_valuation e he F j (Finset.min'_mem _ _)
    (fun _ hi => Finset.min'_le _ _ hi)
  intro hz
  rw [hz, valuation_zero] at hv
  exact WithTop.top_ne_coe hv

/-- Finite surcomplex normal forms are unique for distinct ordered exponents. -/
theorem finiteMonomialEvaluation_injective (e : Γ →+ SignSequence.{u}) (he : StrictMono e) :
    Function.Injective (finiteMonomialEvaluation e) := by
  intro F G h
  have hz : finiteMonomialEvaluation e (F - G) = 0 := by rw [map_sub, h, sub_self]
  have hFG : F - G = 0 := by
    by_contra hFG
    exact finiteMonomialEvaluation_ne_zero e he hFG hz
  exact sub_eq_zero.mp hFG

/-- The actual valuation agrees with the least exponent of the finite Hahn
series, including infinity at zero. -/
theorem valuation_finiteMonomialEvaluation (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (F : AddMonoidAlgebra ℂ Γ) :
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
  rw [finiteMonomialEvaluation_valuation e he F j hj hmin, ho, WithTop.map_coe]

/-- Actual finite surcomplex evaluation preserves the complex leading
coefficient of the associated finite-support Hahn series, including zero. -/
theorem leadingCoeff_finiteMonomialEvaluation (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (F : AddMonoidAlgebra ℂ Γ) :
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

end

end Surreal.Surcomplex
