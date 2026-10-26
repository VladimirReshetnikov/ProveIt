import DiophantineConsistency.HANegativeStability

set_option Elab.async false
namespace DiophantineConsistency.HANegativeStabilityChecks
open SetTheory.PA HA

def body : Formula := .eq (.var 0) (.var 1)

/-- Opening the shifted universal restores both the bound variable and the
free parameter; it does not identify either of them with zero. -/
theorem opened_body :
    Formula.subst (Formula.instTerm (.var 0))
      (Formula.rename (SetTheory.up Nat.succ) (neg body)) = neg body := rfl

theorem shifted_all_elimination :
    Derives [Formula.rename Nat.succ (.all (neg body))] (neg body) := by
  have h := Derives.allE [Formula.rename Nat.succ (.all (neg body))]
    (Formula.rename (SetTheory.up Nat.succ) (neg body))
    (.var 0) (.ass _ (Formula.rename Nat.succ (.all (neg body))) List.mem_cons_self)
  simpa only [Formula.subst_instTerm_var_zero_rename_up_succ] using h

theorem universal_with_open_context :
    Derives [.eq (.var 0) .zero]
      (.imp (doubleNeg (.all (neg body))) (.all (neg body))) :=
  (Negative.all (Negative.neg body)).stable _

theorem negated_existence (a : Formula) :
    Proves (.imp (doubleNeg (neg (.ex a))) (neg (.ex a))) :=
  (Negative.neg (.ex a)).proves_stability

theorem two_binders (a : Formula) :
    Proves (.imp (doubleNeg (.all (.all (neg a)))) (.all (.all (neg a)))) :=
  closeN_neg_stability 2 a

theorem empty_closure (a : Formula) :
    Proves (.imp (doubleNeg (neg a)) (neg a)) := closeN_neg_stability 0 a

/-- This is a generic 14-variable no-equality sentence shape. Binding a
particular polynomial remains a separate source-identification theorem. -/
theorem fourteen_variable_no_equality (s t : Term) :
    Proves (.imp (doubleNeg (Formula.closeN 14 (.imp (.eq s t) .bot)))
      (Formula.closeN 14 (.imp (.eq s t) .bot))) :=
  closeN_neg_stability 14 (.eq s t)

/-- The fragment itself does not admit unrestricted atomic DNE or LEM. This
is a syntactic exclusion, not an independence theorem for HA. -/
theorem atomic_not_in_fragment (s t : Term) : ¬ Negative (.eq s t) := by
  intro h
  cases h

theorem lem_not_in_fragment (a : Formula) : ¬ Negative (.or a (neg a)) := by
  intro h
  cases h

#print axioms Derives.doubleNeg_map
#print axioms Derives.stable_all
#print axioms Negative.stable
#print axioms Negative.proves_stability
#print axioms closeN_neg_stability
#print axioms sealPA_neg_stability
#print axioms universal_with_open_context
#print axioms fourteen_variable_no_equality

end DiophantineConsistency.HANegativeStabilityChecks
