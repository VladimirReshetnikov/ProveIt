import DiophantineConsistency.FoundationHAOrderTrichotomy

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHAOrderTrichotomyChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open FoundationPAHFSyntax FoundationHAOrderTrichotomy SetTheory.PA HA

theorem literal_ltTri : sentence PeanoMinus.Axiom.ltTriᴺ =
    Formula.closeN 2
      (encodedThree (ltFormula (.var 1) (.var 0)) (.eq (.var 1) (.var 0))
        (ltFormula (.var 0) (.var 1))) := rfl

theorem literal_nested_encoding (a b c : Formula) : encodedThree a b c =
    neg (.and (neg (doubleNeg a))
      (neg (neg (.and (neg (doubleNeg b)) (neg (doubleNeg c)))))) := rfl

theorem extra_inner_doubleNeg_changes_formula :
    encodedThree .bot .bot .bot ≠
      neg (.and (neg (doubleNeg .bot))
        (neg (doubleNeg (neg (.and (neg (doubleNeg .bot))
          (neg (doubleNeg .bot))))))) := by
  intro h
  cases h

theorem literal_zero_body : Formula.subst Formula.substZero body =
    .all (tri .zero (.var 0)) := rfl

theorem literal_successor_body : Formula.subst Formula.substSuccVar body =
    .all (tri (.succ (.var 1)) (.var 0)) := rfl

theorem literal_twice_shifted_IH :
    Formula.rename Nat.succ (Formula.rename Nat.succ body) =
      .all (tri (.var 3) (.var 0)) := rfl

theorem shifted_IH_instance :
    Formula.subst (Formula.instTerm (.var 0)) (tri (.var 3) (.var 0)) =
      tri (.var 2) (.var 0) := rfl

theorem literal_lt_succ_witness :
    Formula.subst (Formula.instTerm (.var 7))
      (.eq (.add (.succ (.var 1)) (.succ (.var 0))) (.succ (.var 5))) =
        .eq (.add (.succ (.var 0)) (.succ (.var 7))) (.succ (.var 4)) := rfl

theorem sparse_parameters : Proves (tri
    (.mul (.var 0) (.var 7)) (.add (.var 7) (.succ (.var 0)))) :=
  FoundationHAOrderTrichotomy.trichotomy _ _

theorem context_transport : Relative Formula.Ax_s
    [.eq (.var 7) (.var 4), tri (.var 0) (.var 7)] (tri (.var 0) (.var 4)) :=
  transport_right (Relative.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
    (Relative.hypothesis List.mem_cons_self)

theorem zero_successor : Proves (tri .zero (.succ (.var 7))) := zero_cases _

theorem successor_zero : Proves (tri (.succ (.var 7)) .zero) := succ_zero _

theorem equal_case : Proves (tri (.var 7) (.var 7)) :=
  Relative.or_intro_right _ (Relative.or_intro_left _ (Relative.eq_refl _))

theorem arbitrary_context_encoding {B : Formula → Prop} {G : List Formula}
    {a b c : Formula} (h : Relative B G (.or a (.or b c))) :
    Relative B G (encodedThree a b c) := encoded_three h

theorem nested_formula_encoding : Relative Formula.Ax_s
    [.or (.all (.eq (.var 0) (.var 7)))
      (.or (.ex (.eq (.var 1) (.var 0))) (neg (.eq (.var 0) .zero)))]
    (encodedThree (.all (.eq (.var 0) (.var 7)))
      (.ex (.eq (.var 1) (.var 0))) (neg (.eq (.var 0) .zero))) :=
  encoded_three (Relative.hypothesis List.mem_cons_self)

theorem actual_ltTri : Proves (sentence PeanoMinus.Axiom.ltTriᴺ) :=
  FoundationHAOrderTrichotomy.ltTri

#print axioms transport_right
#print axioms zero_cases
#print axioms succ_zero
#print axioms lt_succ
#print axioms succ_cases
#print axioms tri_all
#print axioms FoundationHAOrderTrichotomy.trichotomy
#print axioms encoded_three
#print axioms FoundationHAOrderTrichotomy.ltTri
#print axioms literal_ltTri
#print axioms literal_nested_encoding
#print axioms extra_inner_doubleNeg_changes_formula
#print axioms literal_zero_body
#print axioms literal_successor_body
#print axioms literal_twice_shifted_IH
#print axioms shifted_IH_instance
#print axioms literal_lt_succ_witness
#print axioms sparse_parameters
#print axioms context_transport
#print axioms zero_successor
#print axioms successor_zero
#print axioms equal_case
#print axioms arbitrary_context_encoding
#print axioms nested_formula_encoding
#print axioms actual_ltTri
end DiophantineConsistency.FoundationHAOrderTrichotomyChecks
