import DiophantineConsistency.FoundationHAOrderDecidable

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHAOrderDecidableChecks
open LO LO.FirstOrder
open scoped LO.FirstOrder
open SetTheory.PA HA FoundationPAHFSyntax FoundationHAOrderDecidable

theorem exact_positive_GG : formula
    (Semiformula.rel .lt ![.fvar 0,.fvar 7] : Proposition ℒₒᵣ)ᴺ =
      doubleNeg (ltFormula (.var 0) (.var 7)) := rfl

theorem actual_atom_recovery : Proves (.imp (formula
    (Semiformula.rel .lt ![.fvar 0,.fvar 7] : Proposition ℒₒᵣ)ᴺ)
    (ltFormula (.var 0) (.var 7))) := lt_stable _ _

theorem sparse_decision : Proves (.or
    (ltFormula (.mul (.var 0) (.var 7)) (.add (.var 7) (.succ (.var 0))))
    (neg (ltFormula (.mul (.var 0) (.var 7)) (.add (.var 7) (.succ (.var 0)))))) :=
  lt_decidable _ _

example : Proves (.or (ltFormula (.var 7) (.var 7))
    (neg (ltFormula (.var 7) (.var 7)))) := lt_decidable _ _
example : Proves (.or (ltFormula .zero (.succ .zero))
    (neg (ltFormula .zero (.succ .zero)))) := lt_decidable _ _

theorem open_transport : Relative Formula.Ax_s
    [.eq (.var 7) (.var 4), ltFormula (.add (.var 0) (.var 7)) (.var 7)]
    (ltFormula (.add (.var 0) (.var 7)) (.var 4)) :=
  transport_right (Relative.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
    (Relative.hypothesis List.mem_cons_self)

theorem shifted_recovery : Relative Formula.Ax_s
    ([doubleNeg (ltFormula (.var 0) (.var 7)), .eq (.var 0) .zero].map
      (Formula.rename Nat.succ)) (ltFormula (.var 1) (.var 8)) := by
  apply recover
  exact Relative.hypothesis List.mem_cons_self

theorem nested_closure : Proves (Formula.closeN 2 (.imp
    (doubleNeg (ltFormula (.add (.var 0) (.var 7)) (.mul (.var 1) (.var 7))))
    (ltFormula (.add (.var 0) (.var 7)) (.mul (.var 1) (.var 7))))) :=
  Arithmetic.reclose 2 (lt_stable _ _)

#print axioms transport_right
#print axioms not_lt_of_eq
#print axioms not_lt_of_reverse
#print axioms lt_decidable
#print axioms lt_stable
#print axioms recover
#print axioms exact_positive_GG
#print axioms actual_atom_recovery
#print axioms sparse_decision
#print axioms open_transport
#print axioms shifted_recovery
#print axioms nested_closure
end DiophantineConsistency.FoundationHAOrderDecidableChecks
