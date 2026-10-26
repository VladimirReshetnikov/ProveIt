import DiophantineConsistency.EnumeratorSemantics

open DiophantineConsistency

/-- The changed actual module has the same literal constructor-only decision. -/
theorem actual_haltingTest_tag_only (t : ℕ) :
    haltingTest t = Encodable.encode
      (@decide (boundedRun t initialState = none)
        (Option.decidableEqNone (boundedRun t initialState))) := rfl

example : haltingTest 0 = 0 := by decide

#print axioms DiophantineConsistency.haltingTest
#print axioms DiophantineConsistency.haltingTest_eq_one_iff
#print axioms DiophantineConsistency.exists_haltingTest_eq_one_iff
#print axioms actual_haltingTest_tag_only
