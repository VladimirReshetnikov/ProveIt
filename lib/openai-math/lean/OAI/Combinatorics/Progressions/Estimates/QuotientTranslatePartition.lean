import Mathlib.MeasureTheory.Measure.Haar.Quotient

namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem additiveFundamentalDomain_op {E : Type*} [AddCommGroup E] [MeasurableSpace E]
    (Γ : AddSubgroup E) {F : Set E} {μ : Measure E}
    (hF : IsAddFundamentalDomain Γ F μ) : IsAddFundamentalDomain Γ.op F μ := by
  have h := hF.preimage_of_equiv (MeasurePreserving.id μ).quasiMeasurePreserving
    (Γ.equivOp.bijective) (fun g x => ?_)
  · exact h
  · change x + (g : E) = (g : E) + x
    exact add_comm _ _

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Set
open scoped Pointwise

theorem quotient_preimage_image_vadd {E : Type*} [AddCommGroup E]
    (Γ : AddSubgroup E) (A : Set E) :
    (QuotientAddGroup.mk : E → E ⧸ Γ) ⁻¹'
      ((QuotientAddGroup.mk : E → E ⧸ Γ) '' A) = ⋃ g : Γ, g +ᵥ A := by
  rw [QuotientAddGroup.preimage_image_mk_eq_iUnion_image]
  congr 1
  funext g
  change (fun x : E => x + g.val) '' A = (fun x : E => g.val + x) '' A
  simp only [add_comm]

theorem quotient_injective_translates_disjoint {E : Type*} [AddCommGroup E]
    (Γ : AddSubgroup E) {A : Set E}
    (hA : InjOn (QuotientAddGroup.mk : E → E ⧸ Γ) A) :
    Pairwise (fun g h : Γ => Disjoint (g +ᵥ A) (h +ᵥ A)) := by
  intro g h hgh
  apply Set.disjoint_left.mpr
  rintro x ⟨a, ha, hga⟩ ⟨b, hb, hhb⟩
  change g.val + a = x at hga
  change h.val + b = x at hhb
  have hg0 : QuotientAddGroup.mk' Γ g.val = 0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr g.property
  have hh0 : QuotientAddGroup.mk' Γ h.val = 0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr h.property
  have hab : a = b := hA ha hb (by
    have he := congrArg (QuotientAddGroup.mk' Γ) (hga.trans hhb.symm)
    simpa only [map_add, hg0, hh0, zero_add, QuotientAddGroup.mk'_apply] using he)
  subst b
  exact hgh (Subtype.ext (add_right_cancel (hga.trans hhb.symm)))

theorem quotient_injective_lift_measure {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (Γ : AddSubgroup E) [Countable Γ]
    (ν : Measure E) [ν.IsAddLeftInvariant]
    {F A : Set E} (hF : IsAddFundamentalDomain Γ F ν) (hFm : MeasurableSet F)
    (hAm : MeasurableSet A) (hA : InjOn (QuotientAddGroup.mk : E → E ⧸ Γ) A) :
    ν (((QuotientAddGroup.mk : E → E ⧸ Γ) ⁻¹'
      ((QuotientAddGroup.mk : E → E ⧸ Γ) '' A)) ∩ F) = ν A := by
  rw [quotient_preimage_image_vadd, Set.iUnion_inter]
  rw [measure_iUnion]
  · exact (hF.measure_eq_tsum A).symm
  · intro g h hgh
    exact (quotient_injective_translates_disjoint Γ hA hgh).mono inter_subset_left inter_subset_left
  · intro g
    exact (hAm.const_vadd g).inter hFm

end Erdos3

end

end OAI
