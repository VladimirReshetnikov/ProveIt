import DiophantineConsistency.FoundationHAOrderAdditive

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHAOrderAdditiveChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open FoundationPAHFSyntax FoundationHAOrderAdditive SetTheory.PA HA

theorem literal_addEqOfLt : sentence PeanoMinus.Axiom.addEqOfLtᴺ =
    Formula.closeN 2 (formula
      (“&1 < &0 → ∃ z, &1 + z = &0” : Proposition ℒₒᵣ)ᴺ) := rfl

theorem literal_addLtAdd : sentence PeanoMinus.Axiom.addLtAddᴺ =
    Formula.closeN 3 (formula
      (“&2 < &1 → &2 + &0 < &1 + &0” : Proposition ℒₒᵣ)ᴺ) := rfl

theorem literal_encoded_exists : formula
    (“∃ z, &1 + z = &0” : Proposition ℒₒᵣ)ᴺ =
      neg (.all (neg (doubleNeg (.eq (.add (.var 2) (.var 0)) (.var 1))))) := rfl

/-- Instantiating the sum witness S d retains both shifted parameters. -/
theorem literal_successor_witness :
    Formula.subst (Formula.instTerm (.succ (.var 0)))
      (addWitnessBody (Term.rename Nat.succ (.var 0))
        (Term.rename Nat.succ (.var 7))) =
      .eq (.add (.var 1) (.succ (.var 0))) (.var 8) := rfl

theorem witness_parameter_not_captured :
    Formula.subst (Formula.instTerm (.succ (.var 0)))
      (addWitnessBody (Term.rename Nat.succ (.var 0))
        (Term.rename Nat.succ (.var 7))) ≠
      .eq (.add (.var 0) (.succ (.var 0))) (.var 7) := by
  intro h
  cases h

theorem encoded_exists_not_witness_extraction :
    neg (.all (neg (doubleNeg (.eq (.var 0) (.var 1))))) ≠
      .ex (.eq (.var 0) (.var 1)) := by
  intro h
  cases h

theorem arbitrary_context_map (B : Formula → Prop) (a b c : Formula) :
    Relative B [.imp a b, c] (.imp (doubleNeg a) (doubleNeg b)) :=
  map_doubleNeg (Relative.hypothesis List.mem_cons_self)

def nestedBody : Formula := .all (.and (.eq (.var 0) (.var 1))
  (.ex (.eq (.var 2) (.var 9))))

theorem nested_existential_context : Relative Formula.Ax_s [.ex nestedBody]
    (neg (.all (neg (doubleNeg nestedBody)))) :=
  encoded_exists (Relative.hypothesis List.mem_cons_self)

def s : Term := .mul (.var 0) (.var 7)
def t : Term := .succ (.var 4)
def u : Term := .add (.var 7) (.var 0)

theorem sparse_add_witness : Relative Formula.Ax_s [ltFormula s t]
    (addWitness s t) := add_witness (Relative.hypothesis List.mem_cons_self)

theorem sparse_add_order : Relative Formula.Ax_s [ltFormula s t]
    (ltFormula (.add s u) (.add t u)) :=
  add_lt_add u (Relative.hypothesis List.mem_cons_self)

theorem sparse_negative_add_witness :
    Relative Formula.Ax_s [doubleNeg (ltFormula s t)]
      (neg (.all (neg (doubleNeg (addWitnessBody s t))))) :=
  negative_add_witness (Relative.hypothesis List.mem_cons_self)

theorem sparse_negative_add_order : Relative Formula.Ax_s [doubleNeg (ltFormula s t)]
    (doubleNeg (ltFormula (.add s u) (.add t u))) :=
  negative_add_lt_add u (Relative.hypothesis List.mem_cons_self)

theorem actual_addEqOfLt : Proves (sentence PeanoMinus.Axiom.addEqOfLtᴺ) :=
  FoundationHAOrderAdditive.addEqOfLt

theorem actual_addLtAdd : Proves (sentence PeanoMinus.Axiom.addLtAddᴺ) :=
  FoundationHAOrderAdditive.addLtAdd

#print axioms map_doubleNeg
#print axioms apply_negative
#print axioms encoded_exists
#print axioms subst_addWitness
#print axioms rename_addWitness
#print axioms add_witness
#print axioms FoundationHAOrderAdditive.add_lt_add
#print axioms negative_add_witness
#print axioms negative_add_lt_add
#print axioms FoundationHAOrderAdditive.addEqOfLt
#print axioms FoundationHAOrderAdditive.addLtAdd
#print axioms LO.FirstOrder.Derivation.imply_doubleNegation
#print axioms literal_addEqOfLt
#print axioms literal_addLtAdd
#print axioms literal_encoded_exists
#print axioms literal_successor_witness
#print axioms witness_parameter_not_captured
#print axioms encoded_exists_not_witness_extraction
#print axioms arbitrary_context_map
#print axioms nested_existential_context
#print axioms sparse_add_witness
#print axioms sparse_add_order
#print axioms sparse_negative_add_witness
#print axioms sparse_negative_add_order
#print axioms actual_addEqOfLt
#print axioms actual_addLtAdd
end DiophantineConsistency.FoundationHAOrderAdditiveChecks
