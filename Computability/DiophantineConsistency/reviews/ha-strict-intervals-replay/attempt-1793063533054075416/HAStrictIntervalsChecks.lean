import DiophantineConsistency.HAStrictIntervals

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.HAStrictIntervalsChecks
open SetTheory.PA HA FoundationPAHFSyntax HAStrictIntervals

theorem zero_interval : Proves (neg (ltFormula (.var 0) .zero)) := not_lt_zero _

theorem zero_successor : Proves (ltFormula .zero (.succ .zero)) := lt_self_succ _

theorem sparse_nested : Proves (.and
    (.imp (ltFormula (.mul (.var 0) (.var 7)) (.succ (.add (.var 4) (.var 0))))
      (.or (ltFormula (.mul (.var 0) (.var 7)) (.add (.var 4) (.var 0)))
        (.eq (.mul (.var 0) (.var 7)) (.add (.var 4) (.var 0)))))
    (.imp (.or (ltFormula (.mul (.var 0) (.var 7)) (.add (.var 4) (.var 0)))
        (.eq (.mul (.var 0) (.var 7)) (.add (.var 4) (.var 0))))
      (ltFormula (.mul (.var 0) (.var 7)) (.succ (.add (.var 4) (.var 0)))))) :=
  lt_succ_iff _ _

theorem open_split : Relative Formula.Ax_s
    [ltFormula (.var 0) (.succ (.var 7)), .eq (.var 4) (.var 0)]
    (.or (ltFormula (.var 0) (.var 7)) (.eq (.var 0) (.var 7))) :=
  lt_succ_split (Relative.hypothesis List.mem_cons_self)

theorem shifted_split : Relative Formula.Ax_s
    ([ltFormula (.var 0) (.succ (.var 7)), .eq (.var 4) (.var 0)].map
      (Formula.rename Nat.succ))
    (.or (ltFormula (.var 1) (.var 8)) (.eq (.var 1) (.var 8))) :=
  lt_succ_split (Relative.hypothesis List.mem_cons_self)

theorem exact_zero_bound : Proves (.imp (ltFormula (.var 7) (.succ .zero))
    (.eq (.var 7) .zero)) := by
  apply Relative.imp_intro
  apply Relative.or_elim (lt_succ_split (Relative.hypothesis List.mem_cons_self))
  · have hb := ((not_lt_zero (.var 7)).weaken (by simp)).mp
      (Relative.hypothesis List.mem_cons_self)
    obtain ⟨L,hL,h⟩ := hb
    exact ⟨L,hL,.botE _ _ h⟩
  · exact Relative.hypothesis List.mem_cons_self

theorem nested_closure : Proves (Formula.closeN 2
    (ltFormula (.add (.var 0) (.var 7)) (.succ (.add (.var 0) (.var 7))))) :=
  Arithmetic.reclose 2 (lt_self_succ _)

#print axioms not_lt_zero
#print axioms lt_self_succ
#print axioms lt_succ_split
#print axioms lt_succ_join
#print axioms lt_succ_iff
#print axioms zero_interval
#print axioms zero_successor
#print axioms sparse_nested
#print axioms open_split
#print axioms shifted_split
#print axioms exact_zero_bound
#print axioms nested_closure
end DiophantineConsistency.HAStrictIntervalsChecks
