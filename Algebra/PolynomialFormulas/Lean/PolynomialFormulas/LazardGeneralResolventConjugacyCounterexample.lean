import PolynomialFormulas.Fin5TransitiveC5
import PolynomialFormulas.LazardGeneralResolventCriterion

/-!
# Why Lazard's resolvent converse yields a conjugate subgroup

For an arbitrary ordering of the roots, a rational root of a separable
relative resolvent selects *some* coset.  Its stabilizer is a conjugate of the
displayed subgroup, and need not be that displayed subgroup itself.

This file records a finite, completely explicit group-level witness.  In
`S5`, conjugate the standard `F20` by the three-cycle `(0 1 2)`.  The resulting
subgroup fixes the corresponding non-base coset of `S5/F20`, but it is not
contained in the displayed standard `F20`; an explicit conjugated five-cycle
witnesses the failure.  Relabelling by the three-cycle converts it back to the
standard subgroup, which is exactly the corrected conclusion used by the
general resolvent criterion.
-/

namespace LeanProofs.PolynomialFormulas.LazardGeneralResolventConjugacyCounterexample

open Equiv MulAction Subgroup
open LeanProofs.PolynomialFormulas.Fin5Solvable
open LeanProofs.PolynomialFormulas.Fin5TransitiveC5

abbrev A := S5
abbrev G : Subgroup A := standardF20
abbrev relabelling : A := threeCycle

/-- The conjugate subgroup selected by the non-base coset. -/
abbrev H : Subgroup A :=
  LazardGeneralResolventCriterion.conjugateStabilizer G relabelling

/-- A concrete element of the conjugate subgroup. -/
def conjugatedFiveCycle : A :=
  relabelling * fiveCycle * relabelling⁻¹

theorem conjugatedFiveCycle_mem_H : conjugatedFiveCycle ∈ H := by
  exact ⟨fiveCycle, Subgroup.le_normalizer (Subgroup.mem_zpowers fiveCycle), rfl⟩

/-- The displayed witness lies outside the standard `F20`.  This is a small
ordinary-kernel finite calculation in `S5`. -/
theorem conjugatedFiveCycle_not_mem_G : conjugatedFiveCycle ∉ G := by
  rw [← mem_f20Elements_iff]
  set_option maxRecDepth 100000 in
    decide

theorem H_not_le_G : ¬ H ≤ G := by
  intro hHG
  exact conjugatedFiveCycle_not_mem_G
    (hHG conjugatedFiveCycle_mem_H)

abbrev Cosets := LazardGeneralResolventCriterion.Cosets G

/-- The non-base coset represented by the relabelling permutation. -/
def selectedCoset : Cosets :=
  relabelling • LazardGeneralResolventCriterion.baseCoset G

/-- Every element of the conjugate subgroup fixes the selected coset. -/
theorem H_fixes_selectedCoset (h : H) :
    h.1 • selectedCoset = selectedCoset := by
  apply MulAction.mem_stabilizer_iff.mp
  change h.1 ∈ MulAction.stabilizer A
    (relabelling • LazardGeneralResolventCriterion.baseCoset G)
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    show MulAction.stabilizer A (LazardGeneralResolventCriterion.baseCoset G) = G by
      simpa only [LazardGeneralResolventCriterion.baseCoset] using
        MulAction.stabilizer_quotient G]
  exact h.2

/-- The same witness does not fix the base coset, because that coset has
stabilizer exactly the displayed standard `F20`. -/
theorem conjugatedFiveCycle_moves_baseCoset :
    conjugatedFiveCycle • LazardGeneralResolventCriterion.baseCoset G ≠
      LazardGeneralResolventCriterion.baseCoset G := by
  intro hfixed
  have hmem : conjugatedFiveCycle ∈
      MulAction.stabilizer A (LazardGeneralResolventCriterion.baseCoset G) :=
    MulAction.mem_stabilizer_iff.mpr hfixed
  have hstabilizer :
      MulAction.stabilizer A (LazardGeneralResolventCriterion.baseCoset G) = G := by
    simpa only [LazardGeneralResolventCriterion.baseCoset] using
      MulAction.stabilizer_quotient G
  exact conjugatedFiveCycle_not_mem_G (hstabilizer ▸ hmem)

/-- Closed group-level counterexample to replacing "a conjugate of `G`" by
the fixed displayed `G` in the converse. -/
theorem fixed_displayed_subgroup_conclusion_fails :
    (∀ h : H, h.1 • selectedCoset = selectedCoset) ∧
      ¬ H ≤ G ∧
      ∃ h : H,
        h.1 • LazardGeneralResolventCriterion.baseCoset G ≠ LazardGeneralResolventCriterion.baseCoset G := by
  refine ⟨H_fixes_selectedCoset, H_not_le_G, ?_⟩
  exact ⟨⟨conjugatedFiveCycle, conjugatedFiveCycle_mem_H⟩,
    conjugatedFiveCycle_moves_baseCoset⟩

end LeanProofs.PolynomialFormulas.LazardGeneralResolventConjugacyCounterexample
