import RamseyPaperCommon.CountCertificates
import DavisEntringerGrahamSimmons1977.Statements
import LeSaulnierVijay2010
import LeSaulnierVijay2011.Statements

/-!
# Paper-facing consequences of the shared counting certificate

The three catalogues use definitionally different names for the same finite
sequence.  This module transports the one expensive certificate to their
exact-value statements and separately checks the corrected `n = 4`
representative list.
-/

set_option autoImplicit false

namespace LeanProofs.RamseyPaperCommon

private theorem davis_values_through_twenty :
    LeanProofs.DavisEntringerGrahamSimmons1977.M 1 = 1 /\
    LeanProofs.DavisEntringerGrahamSimmons1977.M 2 = 2 /\
    LeanProofs.DavisEntringerGrahamSimmons1977.M 3 = 4 /\
    LeanProofs.DavisEntringerGrahamSimmons1977.M 4 = 10 /\
    LeanProofs.DavisEntringerGrahamSimmons1977.M 5 = 20 /\
    LeanProofs.DavisEntringerGrahamSimmons1977.M 6 = 48 /\
    LeanProofs.DavisEntringerGrahamSimmons1977.M 7 = 104 /\
    LeanProofs.DavisEntringerGrahamSimmons1977.M 8 = 282 /\
    LeanProofs.DavisEntringerGrahamSimmons1977.M 9 = 496 /\
    LeanProofs.DavisEntringerGrahamSimmons1977.M 10 = 1066 /\
    LeanProofs.DavisEntringerGrahamSimmons1977.M 11 = 2460 /\
    LeanProofs.DavisEntringerGrahamSimmons1977.M 12 = 6128 /\
    LeanProofs.DavisEntringerGrahamSimmons1977.M 13 = 12840 /\
    LeanProofs.DavisEntringerGrahamSimmons1977.M 14 = 29380 /\
    LeanProofs.DavisEntringerGrahamSimmons1977.M 15 = 74904 /\
    LeanProofs.DavisEntringerGrahamSimmons1977.M 16 = 212728 /\
    LeanProofs.DavisEntringerGrahamSimmons1977.M 17 = 368016 /\
    LeanProofs.DavisEntringerGrahamSimmons1977.M 18 = 659296 /\
    LeanProofs.DavisEntringerGrahamSimmons1977.M 19 = 1371056 /\
    LeanProofs.DavisEntringerGrahamSimmons1977.M 20 = 2937136 := by
  simpa only [reflectedM_eq_davis_M] using reflectedM_values_through_twenty

/-- The two Davis base values used for the elementary recurrence. -/
theorem davis_initial_count_values :
    LeanProofs.DavisEntringerGrahamSimmons1977.initial_count_values := by
  rcases davis_values_through_twenty with ⟨_, h2, h3, _⟩
  exact ⟨h2, h3⟩

/-- The complete corrected Davis table. -/
theorem davis_table_one :
    LeanProofs.DavisEntringerGrahamSimmons1977.table_1 := by
  rcases davis_values_through_twenty with
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
      h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold LeanProofs.DavisEntringerGrahamSimmons1977.table_1
  apply List.ext_get (by simp)
  intro i hi _
  simp only [List.length_ofFn] at hi
  simp only [List.get_eq_getElem, List.getElem_ofFn]
  interval_cases i <;>
    simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
      h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]

private theorem lesaulnier_values_through_twenty :
    LeanProofs.LeSaulnierVijay2011.M 1 = 1 /\
    LeanProofs.LeSaulnierVijay2011.M 2 = 2 /\
    LeanProofs.LeSaulnierVijay2011.M 3 = 4 /\
    LeanProofs.LeSaulnierVijay2011.M 4 = 10 /\
    LeanProofs.LeSaulnierVijay2011.M 5 = 20 /\
    LeanProofs.LeSaulnierVijay2011.M 6 = 48 /\
    LeanProofs.LeSaulnierVijay2011.M 7 = 104 /\
    LeanProofs.LeSaulnierVijay2011.M 8 = 282 /\
    LeanProofs.LeSaulnierVijay2011.M 9 = 496 /\
    LeanProofs.LeSaulnierVijay2011.M 10 = 1066 /\
    LeanProofs.LeSaulnierVijay2011.M 11 = 2460 /\
    LeanProofs.LeSaulnierVijay2011.M 12 = 6128 /\
    LeanProofs.LeSaulnierVijay2011.M 13 = 12840 /\
    LeanProofs.LeSaulnierVijay2011.M 14 = 29380 /\
    LeanProofs.LeSaulnierVijay2011.M 15 = 74904 /\
    LeanProofs.LeSaulnierVijay2011.M 16 = 212728 /\
    LeanProofs.LeSaulnierVijay2011.M 17 = 368016 /\
    LeanProofs.LeSaulnierVijay2011.M 18 = 659296 /\
    LeanProofs.LeSaulnierVijay2011.M 19 = 1371056 /\
    LeanProofs.LeSaulnierVijay2011.M 20 = 2937136 := by
  simpa only [reflectedM_eq_M] using reflectedM_values_through_twenty

/-- The corrected `M(4)` value used by both LeSaulnier--Vijay versions. -/
theorem lesaulnier_M_four_value :
    LeanProofs.LeSaulnierVijay2011.M_four_value := by
  rcases lesaulnier_values_through_twenty with ⟨_, _, _, h4, _⟩
  exact h4

/-- The eight finite values used to initialize Theorem 1. -/
theorem lesaulnier_M_initial_values :
    LeanProofs.LeSaulnierVijay2011.M_initial_values := by
  rcases lesaulnier_values_through_twenty with
    ⟨_, _, _, _, _, _, _, h8, h9, h10, h11, h12, h13, h14, h15, _⟩
  exact ⟨h8, h9, h10, h11, h12, h13, h14, h15⟩

/-- Exhaustive verification of the ten corrected representatives at `n = 4`. -/
theorem lesaulnier_M_four_representatives :
    LeanProofs.LeSaulnierVijay2011.M_four_representatives := by
  unfold LeanProofs.LeSaulnierVijay2011.M_four_representatives
  have checked : forall sigma : Equiv.Perm (Fin 4),
      midpointFreeCheck (LeanProofs.Sharma2012.permutationWord sigma) = true <->
        LeanProofs.LeSaulnierVijay2011.finitePermutationValue sigma = ![1, 3, 4, 2] ∨
        LeanProofs.LeSaulnierVijay2011.finitePermutationValue sigma = ![2, 4, 3, 1] ∨
        LeanProofs.LeSaulnierVijay2011.finitePermutationValue sigma = ![1, 3, 2, 4] ∨
        LeanProofs.LeSaulnierVijay2011.finitePermutationValue sigma = ![4, 2, 3, 1] ∨
        LeanProofs.LeSaulnierVijay2011.finitePermutationValue sigma = ![2, 1, 4, 3] ∨
        LeanProofs.LeSaulnierVijay2011.finitePermutationValue sigma = ![3, 4, 1, 2] ∨
        LeanProofs.LeSaulnierVijay2011.finitePermutationValue sigma = ![2, 4, 1, 3] ∨
        LeanProofs.LeSaulnierVijay2011.finitePermutationValue sigma = ![3, 1, 4, 2] ∨
        LeanProofs.LeSaulnierVijay2011.finitePermutationValue sigma = ![4, 2, 1, 3] ∨
        LeanProofs.LeSaulnierVijay2011.finitePermutationValue sigma = ![3, 1, 2, 4] := by
    native_decide
  intro sigma
  rw [finiteAvoiding_iff_midpointFree, ← midpointFreeCheck_eq_true]
  exact checked sigma

/-- The preprint uses the same corrected value. -/
theorem lesaulnier2010_M_four_value :
    LeanProofs.LeSaulnierVijay2010.M_four_value :=
  lesaulnier_M_four_value

/-- The preprint uses the same corrected finite initialization. -/
theorem lesaulnier2010_M_initial_values :
    LeanProofs.LeSaulnierVijay2010.M_initial_values :=
  lesaulnier_M_initial_values

/-- The preprint and journal catalogues state the same corrected list. -/
theorem lesaulnier2010_M_four_representatives :
    LeanProofs.LeSaulnierVijay2010.M_four_representatives := by
  simpa only [LeanProofs.LeSaulnierVijay2010.M_four_representatives,
    LeanProofs.LeSaulnierVijay2011.M_four_representatives] using
      lesaulnier_M_four_representatives

end LeanProofs.RamseyPaperCommon
