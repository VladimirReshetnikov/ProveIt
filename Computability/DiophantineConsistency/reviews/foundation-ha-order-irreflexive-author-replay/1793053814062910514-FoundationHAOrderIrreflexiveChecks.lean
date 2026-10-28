import DiophantineConsistency.FoundationHAOrderIrreflexive

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHAOrderIrreflexiveChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open FoundationPAHFSyntax FoundationHAOrderIrreflexive SetTheory.PA HA

theorem literal_ltIrrefl : sentence PeanoMinus.Axiom.ltIrreflᴺ =
    Formula.closeN 1 (neg (ltFormula (.var 0) (.var 0))) := rfl

/-- A negative source atom receives one negation, not double negation. -/
theorem no_extra_doubleNeg : sentence PeanoMinus.Axiom.ltIrreflᴺ ≠
    Formula.closeN 1 (doubleNeg (neg (ltFormula (.var 0) (.var 0)))) := by
  intro h
  cases h

theorem literal_parameter_slot : noReturnBody (.var 7) =
    neg (.eq (.add (.var 0) (.succ (.var 8))) (.var 0)) := rfl

theorem literal_zero_step : Formula.subst Formula.substZero (noReturnBody (.var 7)) =
    neg (.eq (.add .zero (.succ (.var 7))) .zero) := rfl

theorem literal_successor_step : Formula.subst Formula.substSuccVar (noReturnBody (.var 7)) =
    neg (.eq (.add (.succ (.var 0)) (.succ (.var 8))) (.succ (.var 0))) := rfl

theorem parameter_is_not_induction_slot : noReturnBody (.var 0) ≠
    neg (.eq (.add (.var 0) (.succ (.var 0))) (.var 0)) := by
  intro h
  cases h

theorem sparse_parameter : Proves (neg (.eq
    (.add (.mul (.var 0) (.var 7)) (.succ (.add (.var 0) (.var 4))))
    (.mul (.var 0) (.var 7)))) := add_succ_ne_self _ _

theorem sparse_irreflexive : Proves (neg (ltFormula
    (.mul (.var 0) (.var 7)) (.mul (.var 0) (.var 7)))) :=
  FoundationHAOrderIrreflexive.lt_irrefl _

theorem context_contradiction : Relative Formula.Ax_s
    [ltFormula (.var 7) (.var 7), .eq (.var 0) (.var 4)] .bot :=
  ((FoundationHAOrderIrreflexive.lt_irrefl (.var 7)).weaken (by simp)).mp
    (Relative.hypothesis List.mem_cons_self)

theorem actual_ltIrrefl : Proves (sentence PeanoMinus.Axiom.ltIrreflᴺ) :=
  FoundationHAOrderIrreflexive.ltIrrefl

#print axioms add_succ_ne_self_all
#print axioms add_succ_ne_self
#print axioms FoundationHAOrderIrreflexive.lt_irrefl
#print axioms FoundationHAOrderIrreflexive.ltIrrefl
#print axioms literal_ltIrrefl
#print axioms no_extra_doubleNeg
#print axioms literal_parameter_slot
#print axioms literal_zero_step
#print axioms literal_successor_step
#print axioms parameter_is_not_induction_slot
#print axioms sparse_parameter
#print axioms sparse_irreflexive
#print axioms context_contradiction
#print axioms actual_ltIrrefl
end DiophantineConsistency.FoundationHAOrderIrreflexiveChecks
