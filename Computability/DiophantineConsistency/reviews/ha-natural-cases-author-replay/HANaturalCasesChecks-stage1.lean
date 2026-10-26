import DiophantineConsistency.HANaturalCases

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.HANaturalCasesChecks
open SetTheory.PA DiophantineConsistency.HA

theorem literal_closed_case_split : Proves (.all (.or (.eq (.var 0) .zero)
    (.ex (.eq (.var 1) (.succ (.var 0)))))) := NaturalCases.zero_or_succ_all

theorem ambient_variables_not_captured : Proves
    (.or (.eq (.add (.var 0) (.var 4)) .zero)
      (.ex (.eq (.add (.var 1) (.var 5)) (.succ (.var 0))))) :=
  NaturalCases.zero_or_succ (.add (.var 0) (.var 4))

theorem nested_term_not_captured : Proves
    (.or (.eq (.mul (.succ (.var 2)) (.add (.var 0) (.var 3))) .zero)
      (.ex (.eq (.mul (.succ (.var 3)) (.add (.var 1) (.var 4))) (.succ (.var 0))))) :=
  NaturalCases.zero_or_succ (.mul (.succ (.var 2)) (.add (.var 0) (.var 3)))

example : Formula.subst Formula.substZero NaturalCases.body =
    .or (.eq .zero .zero) (.ex (.eq .zero (.succ (.var 0)))) := NaturalCases.body_zero

example : Formula.subst Formula.substSuccVar NaturalCases.body =
    .or (.eq (.succ (.var 0)) .zero)
      (.ex (.eq (.succ (.var 1)) (.succ (.var 0)))) := NaturalCases.body_succ

theorem successor_witness_with_parameter : Proves
    (.ex (.eq (.succ (.add (.var 1) (.var 5))) (.succ (.var 0)))) :=
  NaturalCases.succ_has_predecessor (.add (.var 0) (.var 4))

theorem actual_split_is_sentence : Formula.Sentence (.all NaturalCases.body) := by
  intro n hn
  change (n+1 = 0 ∨ False) ∨ (n+2 = 1 ∨ n+2 = 0) at hn
  omega

theorem close_term_parameters (n : Nat) (t : Term) : Proves
    (Formula.closeN n (.or (.eq t .zero)
      (.ex (.eq (Term.rename Nat.succ t) (.succ (.var 0)))))) :=
  Arithmetic.reclose n (NaturalCases.zero_or_succ t)

#print axioms Relative.or_intro_left
#print axioms Relative.or_intro_right
#print axioms Relative.ex_intro
#print axioms NaturalCases.body_inst
#print axioms NaturalCases.zero_or_succ_all
#print axioms NaturalCases.zero_or_succ
#print axioms NaturalCases.succ_has_predecessor
#print axioms ambient_variables_not_captured
#print axioms nested_term_not_captured
#print axioms actual_split_is_sentence
#print axioms close_term_parameters

end DiophantineConsistency.HANaturalCasesChecks
