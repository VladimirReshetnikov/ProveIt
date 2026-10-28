import DiophantineConsistency.FoundationHAOrderMultiplicative

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHAOrderMultiplicativeChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open FoundationPAHFSyntax FoundationHAOrderMultiplicative SetTheory.PA HA

theorem literal_mulLtMul : sentence PeanoMinus.Axiom.mulLtMulᴺ =
    Formula.closeN 3 (formula
      (“&2 < &1 ∧ 0 < &0 → &2 * &0 < &1 * &0” : Proposition ℒₒᵣ)ᴺ) := rfl

theorem literal_premise : formula (“&2 < &1 ∧ 0 < &0” : Proposition ℒₒᵣ)ᴺ =
    .and (doubleNeg (ltFormula (.var 2) (.var 1)))
      (doubleNeg (ltFormula .zero (.var 0))) := rfl

theorem positive_multiplier_not_deleted :
    formula (“&2 < &1 ∧ 0 < &0” : Proposition ℒₒᵣ)ᴺ ≠
      formula (“&2 < &1” : Proposition ℒₒᵣ)ᴺ := by
  intro h
  cases h

/-- d,e stay in slots1,0 while the multiplier keeps its twice-shifted slot. -/
theorem literal_product_witness : Formula.subst
    (Formula.instTerm (.add (.mul (.var 1) (.var 9)) (.var 0)))
    (.eq (.add (Term.rename Nat.succ (.mul (.var 2) (.var 9))) (.succ (.var 0)))
      (Term.rename Nat.succ (.mul (.var 6) (.var 9)))) =
    .eq (.add (.mul (.var 2) (.var 9))
      (.succ (.add (.mul (.var 1) (.var 9)) (.var 0)))) (.mul (.var 6) (.var 9)) := rfl

theorem two_witness_slots : (Term.add (.mul (.var 1) (.var 9)) (.var 0)) ≠
    .add (.mul (.var 0) (.var 9)) (.var 1) := by
  intro h
  cases h

def s : Term := .mul (.var 0) (.var 7)
def t : Term := .succ (.var 4)
def u : Term := .add (.var 7) (.var 0)

theorem sparse_ordinary : Relative Formula.Ax_s
    [ltFormula s t, ltFormula .zero u, .eq (.var 7) (.var 0)]
    (ltFormula (.mul s u) (.mul t u)) :=
  FoundationHAOrderMultiplicative.mul_lt_mul (Relative.hypothesis List.mem_cons_self)
    (Relative.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))

theorem sparse_negative : Relative Formula.Ax_s
    [doubleNeg (ltFormula s t), doubleNeg (ltFormula .zero u)]
    (doubleNeg (ltFormula (.mul s u) (.mul t u))) :=
  negative_mul_lt_mul (Relative.hypothesis List.mem_cons_self)
    (Relative.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))

theorem unit_multiplier : Proves (ltFormula (.mul .zero (.succ .zero))
    (.mul (.succ .zero) (.succ .zero))) :=
  FoundationHAOrderMultiplicative.mul_lt_mul FoundationHAOrderBase.zero_lt_one
    FoundationHAOrderBase.zero_lt_one

theorem actual_mulLtMul : Proves (sentence PeanoMinus.Axiom.mulLtMulᴺ) :=
  FoundationHAOrderMultiplicative.mulLtMul

#print axioms mul_lt_mul_imp
#print axioms FoundationHAOrderMultiplicative.mul_lt_mul
#print axioms negative_mul_lt_mul
#print axioms FoundationHAOrderMultiplicative.mulLtMul
#print axioms LO.FirstOrder.Derivation.imply_doubleNegation
#print axioms literal_mulLtMul
#print axioms literal_premise
#print axioms positive_multiplier_not_deleted
#print axioms literal_product_witness
#print axioms two_witness_slots
#print axioms sparse_ordinary
#print axioms sparse_negative
#print axioms unit_multiplier
#print axioms actual_mulLtMul
end DiophantineConsistency.FoundationHAOrderMultiplicativeChecks
