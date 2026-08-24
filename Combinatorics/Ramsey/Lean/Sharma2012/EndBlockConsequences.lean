import Sharma2012.ReflectionConsequences

/-!
# Sharp active end-block consequences

The reflection construction turns the second implication of Theorem 2.7 into
the already proved first implication.  For odd ambient sizes, deleting the
maximum can enlarge the transformed even active block, so the argument uses
the one-sided length comparison from `ReflectionConsequences` rather than a
false equality.
-/

set_option autoImplicit false

namespace LeanProofs.Sharma2012

/-- The second implication of Theorem 2.7, conditional on Theorem 2.6.
The transformed odd active length is exactly the original even active length,
while the transformed even active length bounds the original odd active
length from above. -/
theorem theorem_2_7_right_of_theorem_2_6 (h₂₆ : theorem_2_6) :
    ∀ (n : Nat) (gamma : List Nat), StandingInterleavingHypotheses n gamma →
      5 ≤ (prologue n (evenTrace gamma)).length →
        (epilogue n (oddTrace gamma)).length = 1 := by
  intro n gamma hstanding hv
  let N := reflectedActiveAmbient n
  let delta := reflectedActiveWord n gamma
  have hdeltaStanding : StandingInterleavingHypotheses N delta := by
    simpa only [N, delta] using reflectedActiveWord_standing hstanding
  have hdeltaOddFive : 5 ≤ (epilogue N (oddTrace delta)).length := by
    change 5 ≤ (oddBoundaryActiveList N delta).length
    rw [show oddBoundaryActiveList N delta = reflectedOddActiveList n gamma by
      simpa only [N, delta] using
        oddBoundaryActiveList_reflectedActiveWord hstanding.1.1]
    simpa only [reflectedOddActiveList_length] using hv
  have hdeltaEvenOne : (prologue N (evenTrace delta)).length = 1 :=
    theorem_2_7_left_of_theorem_2_6 h₂₆ N delta hdeltaStanding hdeltaOddFive
  have hmonotone := oddBoundaryActiveList_length_le_reflected_even hstanding
  have huUpper : (epilogue n (oddTrace gamma)).length ≤ 1 := by
    change (oddBoundaryActiveList n gamma).length ≤ 1
    exact hmonotone.trans (by
      simpa only [N, delta, evenBoundaryActiveList_length] using hdeltaEvenOne.le)
  rcases hstanding.2 with
    ⟨b, c, hbEnd, hcStart, hcommute, hbLower, hcUpper⟩
  have hBStart : StartsWith (epilogue n (oddTrace gamma)) b := by
    simpa only [epilogue] using startsWith_prologue_of_startsWith
      (n := n) (startsWith_reversal_of_endsWith hbEnd)
  have huPositive : 0 < (epilogue n (oddTrace gamma)).length := by
    exact List.length_pos_of_ne_nil
      (List.ne_nil_of_mem (mem_of_startsWith hBStart))
  omega

/-- **Theorem 2.7.** If either active end block has length at least five,
the other has length exactly one. -/
theorem theorem_2_7_holds : theorem_2_7 := by
  intro n gamma hstanding
  dsimp only
  exact ⟨theorem_2_7_left_of_theorem_2_6 theorem_2_6_holds n gamma hstanding,
    theorem_2_7_right_of_theorem_2_6 theorem_2_6_holds n gamma hstanding⟩

end LeanProofs.Sharma2012
