/-
Modified for ProveIt: use Set.restrict, the Mathlib 4.32 name for the
domain restriction in the measurable fundamental-domain representative.
All theorem statements are unchanged from the pinned upstream source.
-/
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic

namespace OAI

section

open MeasureTheory Module

namespace Erdos3

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]

theorem exists_measurable_representative_zspan (b : Basis I ℝ E) :
    ∃ r : E ⧸ (Submodule.span ℤ (Set.range b)).toAddSubgroup → E,
      Measurable r ∧ ∀ x,
        QuotientAddGroup.mk' (Submodule.span ℤ (Set.range b)).toAddSubgroup (r x) = x := by
  let e : E ⧸ (Submodule.span ℤ (Set.range b)).toAddSubgroup ≃
      ZSpan.fundamentalDomain b := ZSpan.quotientEquiv b
  have hsymm (x : ZSpan.fundamentalDomain b) :
      e.symm x = QuotientAddGroup.mk' (Submodule.span ℤ (Set.range b)).toAddSubgroup (x : E) := by
    exact ZSpan.quotientEquiv.symm_apply b x
  have hcont : Continuous (fun x : E =>
      (QuotientAddGroup.mk' (Submodule.span ℤ (Set.range b)).toAddSubgroup) x) :=
    QuotientAddGroup.continuous_mk
  have hinj : Set.InjOn
      (QuotientAddGroup.mk' (Submodule.span ℤ (Set.range b)).toAddSubgroup)
      (ZSpan.fundamentalDomain b) := by
    intro x hx y hy hxy
    have he : e.symm ⟨x, hx⟩ = e.symm ⟨y, hy⟩ := by
      simpa only [hsymm] using hxy
    exact congrArg Subtype.val (e.symm.injective he)
  have hfun : (e.symm : ZSpan.fundamentalDomain b → _) =
      (ZSpan.fundamentalDomain b).restrict
        (QuotientAddGroup.mk' (Submodule.span ℤ (Set.range b)).toAddSubgroup) :=
    funext hsymm
  have hem : MeasurableEmbedding (e.symm : ZSpan.fundamentalDomain b → _) := by
    rw [hfun]
    exact hcont.continuousOn.measurableEmbedding (ZSpan.fundamentalDomain_measurableSet b) hinj
  have he : Measurable e := hem.measurable_comp_iff.mp (by simpa using measurable_id)
  refine ⟨fun x => (e x : E), measurable_subtype_coe.comp he, ?_⟩
  intro x
  simpa only [hsymm] using e.symm_apply_apply x

theorem lattice_exists_measurable_representative (Λ : Submodule ℤ E)
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (b : Basis I ℤ Λ) :
    ∃ r : E ⧸ Λ.toAddSubgroup → E,
      Measurable r ∧ ∀ x, QuotientAddGroup.mk' Λ.toAddSubgroup (r x) = x := by
  have hspan : Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ Λ : I → E)) = Λ :=
    b.ofZLatticeBasis_span ℝ Λ
  rw [← hspan]
  exact exists_measurable_representative_zspan (b.ofZLatticeBasis ℝ Λ)

end Erdos3

end

end OAI
