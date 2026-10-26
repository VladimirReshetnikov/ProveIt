import DiophantineConsistency.FoundationHAArithmetic

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHAArithmeticChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open FoundationPAHFSyntax FoundationHAArithmetic
open SetTheory.PA

theorem addZero_image : sentence PeanoMinus.Axiom.addZeroᴺ =
    Formula.closeN 1 (HA.doubleNeg (.eq (.add (.var 0) .zero) (.var 0))) := rfl
theorem addAssoc_image : sentence PeanoMinus.Axiom.addAssocᴺ =
    Formula.closeN 3 (HA.doubleNeg (.eq (.add (.add (.var 2) (.var 1)) (.var 0))
      (.add (.var 2) (.add (.var 1) (.var 0))))) := rfl
theorem addComm_image : sentence PeanoMinus.Axiom.addCommᴺ =
    Formula.closeN 2 (HA.doubleNeg (.eq (.add (.var 1) (.var 0))
      (.add (.var 0) (.var 1)))) := rfl
theorem mulZero_image : sentence PeanoMinus.Axiom.mulZeroᴺ =
    Formula.closeN 1 (HA.doubleNeg (.eq (.mul (.var 0) .zero) .zero)) := rfl
theorem mulOne_image : sentence PeanoMinus.Axiom.mulOneᴺ =
    Formula.closeN 1 (HA.doubleNeg (.eq (.mul (.var 0) (.succ .zero)) (.var 0))) := rfl
theorem mulAssoc_image : sentence PeanoMinus.Axiom.mulAssocᴺ =
    Formula.closeN 3 (HA.doubleNeg (.eq (.mul (.mul (.var 2) (.var 1)) (.var 0))
      (.mul (.var 2) (.mul (.var 1) (.var 0))))) := rfl
theorem mulComm_image : sentence PeanoMinus.Axiom.mulCommᴺ =
    Formula.closeN 2 (HA.doubleNeg (.eq (.mul (.var 1) (.var 0))
      (.mul (.var 0) (.var 1)))) := rfl
theorem distr_image : sentence PeanoMinus.Axiom.distrᴺ =
    Formula.closeN 3 (HA.doubleNeg (.eq (.mul (.var 2) (.add (.var 1) (.var 0)))
      (.add (.mul (.var 2) (.var 1)) (.mul (.var 2) (.var 0))))) := rfl

/-- The actual translated two-quantifier axiom opens at arbitrary terms. -/
theorem translated_open (s t : Term) : HA.Proves (HA.doubleNeg
    (.eq (.add s t) (.add t s))) := by
  have hc : HA.Proves (.all (.all (HA.doubleNeg (.eq
      (.add (.var 1) (.var 0)) (.add (.var 0) (.var 1)))))) := addComm
  have h := HA.Relative.all_elim t (HA.Relative.all_elim s hc)
  simpa only [HA.Proves, HA.doubleNeg, HA.neg, Formula.subst, Term.subst,
    Term.upSubst, Formula.instTerm, Formula.term_subst_instTerm_rename_succ] using h

example : HA.Proves (HA.doubleNeg (.eq
    (.add (.mul (.var 0) (.var 4)) (.succ (.add (.var 3) (.var 1))))
    (.add (.succ (.add (.var 3) (.var 1))) (.mul (.var 0) (.var 4))))) :=
  translated_open (.mul (.var 0) (.var 4)) (.succ (.add (.var 3) (.var 1)))

/-- Foundation's constant one is literally successor-zero in this interpretation. -/
theorem constant_one : term (.func .one Fin.elim0 : SyntacticTerm ℒₒᵣ) = .succ .zero := rfl

/-- A concrete order axiom is outside the exact list this packet discharges. -/
theorem order_not_in_equations : PeanoMinus.Axiom.ltIrrefl ∉ semiringAxioms := by
  intro h
  simp only [semiringAxioms, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h <;> cases h

example {σ : ArithmeticSentence} (h : σ ∈ semiringAxioms) :
    PeanoMinus σ ∧ HA.Proves (sentence σᴺ) :=
  ⟨semiringAxioms_subset h, semiring_axiom h⟩

#print axioms FoundationHAArithmetic.addZero
#print axioms FoundationHAArithmetic.addAssoc
#print axioms FoundationHAArithmetic.addComm
#print axioms FoundationHAArithmetic.mulZero
#print axioms FoundationHAArithmetic.mulOne
#print axioms FoundationHAArithmetic.mulAssoc
#print axioms FoundationHAArithmetic.mulComm
#print axioms FoundationHAArithmetic.distr
#print axioms semiringAxioms_length
#print axioms semiringAxioms_subset
#print axioms semiring_axiom
#print axioms addZero_image
#print axioms addAssoc_image
#print axioms addComm_image
#print axioms mulZero_image
#print axioms mulOne_image
#print axioms mulAssoc_image
#print axioms mulComm_image
#print axioms distr_image
#print axioms translated_open
#print axioms constant_one
#print axioms order_not_in_equations
end DiophantineConsistency.FoundationHAArithmeticChecks
