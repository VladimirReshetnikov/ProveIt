import DiophantineConsistency.FoundationHAOrderWitnesses

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHAOrderWitnessesChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open FoundationPAHFSyntax FoundationHAOrderWitnesses SetTheory.PA HA

theorem literal_oneLeOfZeroLt : sentence PeanoMinus.Axiom.oneLeOfZeroLtᴺ =
    Formula.closeN 1 (formula (“0 < &0 → 1 ≤ &0” : Proposition ℒₒᵣ)ᴺ) := rfl

theorem literal_ltTrans : sentence PeanoMinus.Axiom.ltTransᴺ =
    Formula.closeN 3 (formula
      (“&2 < &1 ∧ &1 < &0 → &2 < &0” : Proposition ℒₒᵣ)ᴺ) := rfl

theorem literal_oneLe_consequent : formula (“1 ≤ &0” : Proposition ℒₒᵣ)ᴺ =
    neg (.and (neg (doubleNeg (.eq (.succ .zero) (.var 0))))
      (neg (doubleNeg (ltFormula (.succ .zero) (.var 0))))) := rfl

theorem literal_trans_premise : formula
    (“&2 < &1 ∧ &1 < &0” : Proposition ℒₒᵣ)ᴺ =
      .and (doubleNeg (ltFormula (.var 2) (.var 1)))
        (doubleNeg (ltFormula (.var 1) (.var 0))) := rfl

/-- The first predecessor moves to slot1; ambient parameters shift twice. -/
theorem first_witness_preserved : Formula.rename Nat.succ
    (.eq (.add (Term.rename Nat.succ (.var 0)) (.succ (.var 0)))
      (Term.rename Nat.succ (.var 7))) =
      .eq (.add (.var 2) (.succ (.var 1))) (.var 9) := rfl

theorem literal_trans_witness :
    Formula.subst (Formula.instTerm (.add (.succ (.var 1)) (.var 0)))
      (.eq (.add (Term.rename Nat.succ (.var 2)) (.succ (.var 0)))
        (Term.rename Nat.succ (.var 9))) =
      .eq (.add (.var 2) (.succ (.add (.succ (.var 1)) (.var 0)))) (.var 9) := rfl

theorem witnesses_are_distinct_slots :
    (Term.add (.succ (.var 1)) (.var 0)) ≠ .add (.succ (.var 0)) (.var 1) := by
  intro h
  cases h

theorem zero_predecessor_case : Proves (.or (.eq (.succ .zero) (.succ .zero))
    (ltFormula (.succ .zero) (.succ .zero))) :=
  FoundationHAOrderWitnesses.one_le_of_zero_lt FoundationHAOrderBase.zero_lt_one

theorem successor_predecessor_case : Proves (.or
    (.eq (.succ .zero) (.succ (.succ .zero)))
    (ltFormula (.succ .zero) (.succ (.succ .zero)))) := by
  apply FoundationHAOrderWitnesses.one_le_of_zero_lt
  apply Relative.ex_intro _ (.succ .zero)
  exact Arithmetic.zero_add (.succ (.succ .zero))

theorem arbitrary_pair_context (B : Formula → Prop) (a b c : Formula) :
    Relative B [doubleNeg a, doubleNeg b, c] (doubleNeg (.and a b)) :=
  pair_doubleNeg (Relative.hypothesis List.mem_cons_self)
    (Relative.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))

def s : Term := .mul (.var 0) (.var 7)
def t : Term := .succ (.var 4)
def u : Term := .add (.var 7) (.var 0)

theorem sparse_one_le : Relative Formula.Ax_s [ltFormula .zero t]
    (.or (.eq (.succ .zero) t) (ltFormula (.succ .zero) t)) :=
  FoundationHAOrderWitnesses.one_le_of_zero_lt (Relative.hypothesis List.mem_cons_self)

theorem sparse_trans : Relative Formula.Ax_s
    [ltFormula s t, ltFormula t u, .eq (.var 7) (.var 0)] (ltFormula s u) :=
  FoundationHAOrderWitnesses.lt_trans (Relative.hypothesis List.mem_cons_self)
    (Relative.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))

theorem sparse_negative_trans : Relative Formula.Ax_s
    [doubleNeg (ltFormula s t), doubleNeg (ltFormula t u)]
    (doubleNeg (ltFormula s u)) :=
  negative_lt_trans (Relative.hypothesis List.mem_cons_self)
    (Relative.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))

theorem actual_oneLeOfZeroLt : Proves (sentence PeanoMinus.Axiom.oneLeOfZeroLtᴺ) :=
  FoundationHAOrderWitnesses.oneLeOfZeroLt

theorem actual_ltTrans : Proves (sentence PeanoMinus.Axiom.ltTransᴺ) :=
  FoundationHAOrderWitnesses.ltTrans

#print axioms pair_doubleNeg
#print axioms FoundationHAOrderWitnesses.one_le_of_zero_lt
#print axioms lt_trans_imp
#print axioms FoundationHAOrderWitnesses.lt_trans
#print axioms negative_one_le
#print axioms negative_lt_trans
#print axioms FoundationHAOrderWitnesses.oneLeOfZeroLt
#print axioms FoundationHAOrderWitnesses.ltTrans
#print axioms LO.FirstOrder.Derivation.imply_doubleNegation
#print axioms literal_oneLeOfZeroLt
#print axioms literal_ltTrans
#print axioms literal_oneLe_consequent
#print axioms literal_trans_premise
#print axioms first_witness_preserved
#print axioms literal_trans_witness
#print axioms witnesses_are_distinct_slots
#print axioms zero_predecessor_case
#print axioms successor_predecessor_case
#print axioms arbitrary_pair_context
#print axioms sparse_one_le
#print axioms sparse_trans
#print axioms sparse_negative_trans
#print axioms actual_oneLeOfZeroLt
#print axioms actual_ltTrans
end DiophantineConsistency.FoundationHAOrderWitnessesChecks
