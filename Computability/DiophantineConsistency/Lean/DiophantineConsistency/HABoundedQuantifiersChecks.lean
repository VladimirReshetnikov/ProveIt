import DiophantineConsistency.HABoundedQuantifiers

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.HABoundedQuantifiersChecks
open SetTheory.PA HA HABoundedQuantifiers FoundationPAHFSyntax

def matrix : Formula := .all (.or (.eq (.var 1) (.var 8))
  (.ex (.eq (.add (.var 2) (.var 0)) (.var 6))))
def bound : Term := .mul (.add (.var 0) (.var 7)) (.succ (.var 4))

example : ball bound matrix = .all (.imp
    (ltFormula (.var 0) (.mul (.add (.var 1) (.var 8)) (.succ (.var 5)))) matrix) := rfl
example : plus matrix = .all (.or (.eq (.var 1) (.var 9))
    (.ex (.eq (.add (.var 2) (.var 0)) (.var 7)))) := rfl
example : inst (plus matrix) (.var 0) = matrix := inst_plus_zero _
example : Formula.subst (Term.upSubst (Formula.instTerm bound)) (plus matrix) = matrix :=
  drop_parameter _ _

theorem arbitrary_nested_all : Proves (.imp (.all (dec matrix)) (dec (ball bound matrix))) :=
  ball_decidable _ _
theorem arbitrary_nested_ex : Proves (.imp (.all (dec matrix)) (dec (bex bound matrix))) :=
  bex_decidable _ _
theorem open_context : Relative Formula.Ax_s [.all (dec matrix), .eq (.var 4) .zero]
    (dec (ball bound matrix)) :=
  ((ball_decidable bound matrix).weaken (by simp)).mp
    (Relative.hypothesis List.mem_cons_self)
theorem shifted_context : Relative Formula.Ax_s
    ([.all (dec matrix), .eq (.var 4) .zero].map (Formula.rename Nat.succ))
    (dec (ball (Term.rename Nat.succ bound) (plus matrix))) :=
  ((ball_decidable _ _).weaken (by simp)).mp (Relative.hypothesis List.mem_cons_self)
theorem empty_all : Proves (ball .zero matrix) := ball_zero _
theorem empty_ex_false : Proves (neg (bex .zero matrix)) := not_bex_zero _
theorem bound_one : Proves (.imp (bex (.succ .zero) matrix)
    (.or (bex .zero matrix) (inst matrix .zero))) := bex_succ_forward _ _
theorem unrestricted_matrix (a : Formula) : Proves
    (.imp (.all (dec a)) (dec (bex (.var 0) a))) := bex_decidable _ _

#print axioms ball_zero
#print axioms not_bex_zero
#print axioms ball_succ_forward
#print axioms ball_succ_reverse
#print axioms bex_succ_forward
#print axioms bex_succ_reverse
#print axioms decisions_all
#print axioms ball_decidable
#print axioms bex_decidable
#print axioms arbitrary_nested_all
#print axioms arbitrary_nested_ex
#print axioms open_context
#print axioms shifted_context
#print axioms empty_all
#print axioms empty_ex_false
#print axioms bound_one
#print axioms unrestricted_matrix
end DiophantineConsistency.HABoundedQuantifiersChecks
