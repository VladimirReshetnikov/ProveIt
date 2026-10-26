import DiophantineConsistency.HAEqualityDecidable

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.HAEqualityDecidableChecks
open SetTheory.PA DiophantineConsistency.HA

theorem literal_two_variable_sentence : Proves (.all (.all
    (.or (.eq (.var 1) (.var 0)) (.imp (.eq (.var 1) (.var 0)) .bot)))) :=
  EqualityDecidable.eq_decidable_all

theorem shared_free_parameters : Proves
    (.or (.eq (.add (.var 0) (.var 4)) (.succ (.var 0)))
      (.imp (.eq (.add (.var 0) (.var 4)) (.succ (.var 0))) .bot)) :=
  EqualityDecidable.eq_decidable (.add (.var 0) (.var 4)) (.succ (.var 0))

theorem distinct_nested_parameters : Proves
    (EqualityDecidable.cases (.mul (.var 3) (.add (.var 0) (.var 7)))
      (.add (.succ (.var 2)) (.var 0))) :=
  EqualityDecidable.eq_decidable (.mul (.var 3) (.add (.var 0) (.var 7)))
    (.add (.succ (.var 2)) (.var 0))

/-- The arbitrary free-variable assumption is shifted, not discharged or
replaced by a closed formula, while the existential witness is eliminated. -/
theorem open_assumption_survives (B : Formula → Prop) (hB : Formula.Sentences B) :
    Relative B [.eq (.var 0) (.var 4), .ex (.eq (.var 0) (.var 0))]
      (.eq (.var 0) (.var 4)) := by
  apply Relative.ex_elim hB
    (Relative.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
  change Relative B [.eq (.var 0) (.var 0), .eq (.var 1) (.var 5),
      .ex (.eq (.var 0) (.var 0))] (.eq (.var 1) (.var 5))
  exact Relative.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)

theorem actual_statement_closed : Formula.Sentence (.all EqualityDecidable.body) := by
  intro n hn
  change (n+2 = 1 ∨ n+2 = 0) ∨ ((n+2 = 1 ∨ n+2 = 0) ∨ False) at hn
  rcases hn with (hn | hn) | ((hn | hn) | hn)
  · omega
  · omega
  · omega
  · omega
  · exact hn

theorem close_arbitrary_parameters (n : Nat) (s t : Term) :
    Proves (Formula.closeN n (EqualityDecidable.cases s t)) :=
  Arithmetic.reclose n (EqualityDecidable.eq_decidable s t)

#print axioms Relative.hypothesis
#print axioms Relative.or_elim
#print axioms Relative.ex_elim
#print axioms Relative.eq_elim
#print axioms EqualityDecidable.transport_right
#print axioms EqualityDecidable.zero_cases
#print axioms EqualityDecidable.succ_cases
#print axioms EqualityDecidable.eq_decidable_all
#print axioms EqualityDecidable.eq_decidable
#print axioms shared_free_parameters
#print axioms distinct_nested_parameters
#print axioms open_assumption_survives
#print axioms actual_statement_closed
#print axioms close_arbitrary_parameters

end DiophantineConsistency.HAEqualityDecidableChecks
