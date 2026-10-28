import DiophantineConsistency.FoundationHANoZero

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHANoZeroChecks
open LO LO.FirstOrder
open scoped LO.FirstOrder
open SetTheory.PA HA FoundationPAHFSyntax FoundationHANoZero

theorem last_of_fourteen : sourceTerm 14 (.var 13) =
    (Semiterm.bvar (13 : Fin 14) : Semiterm ℒₒᵣ Empty 14) := rfl

theorem out_of_range_is_zero : slot 14 14 =
    (Semiterm.func .zero Fin.elim0 : Semiterm ℒₒᵣ Empty 14) := rfl

theorem successor_is_add_one : translatedTerm 14 (.succ (.var 13)) =
    .add (.var 13) (.succ .zero) := rfl

/-- The needed equality is an HA theorem, not definitional equality. -/
theorem successor_not_definitional : translatedTerm 14 (.succ (.var 13)) ≠
    .succ (.var 13) := by
  intro h
  cases h

theorem successor_proof : Proves (.eq (translatedTerm 14 (.succ (.var 13)))
    (.succ (.var 13))) :=
  translatedTerm_correct 14 _ (fun _ h => by cases h; decide)

theorem odd_numeral_literal : translatedTerm 0 (ArithmeticExpression.binaryNumeral 1) =
    .add (.mul (.add (.add .zero (.succ .zero)) (.succ .zero)) .zero) (.succ .zero) := by
  decide +kernel

theorem arbitrary_binary_proof (n k : ℕ) :
    Proves (.eq (translatedTerm n (ArithmeticExpression.binaryNumeral k))
      (ArithmeticExpression.binaryNumeral k)) := binaryNumeral_correct n k

theorem separate_environments : Proves (.eq
    (.add (.add (.var 7) (.var 14)) (.succ .zero))
    (.succ (.add (.var 7) (.var 14)))) := by
  let env : ℕ → Semiterm ℒₒᵣ ℕ 1 :=
    fun i => if i = 0 then .bvar 0 else .fvar (i+3)
  exact reflectTerm_correct (fun _ : Fin 1 => .var 7) (fun j => .var (j+10)) env
    (.succ (.add (.var 0) (.var 1)))

theorem positive_input_literal : ArithmeticExpression.term Fin.val
    (.add (.var (0 : Fin 1)) (.constant 1)) =
      .add (.var 0) (ArithmeticExpression.binaryNumeral 1) := rfl

theorem zero_variable_GG (z : ℤ) :
    sentence (classicalNoZero (.constant z : Expr (Fin 0)))ᴺ =
      neg (reflectedEquation (.constant z : Expr (Fin 0))) :=
  translated_classicalNoZero _

theorem two_variable_GG (e : Expr (Fin 2)) :
    sentence (classicalNoZero e)ᴺ = .all (.all (neg (reflectedEquation e))) :=
  translated_classicalNoZero e

theorem no_extra_GG_doubleNeg :
    sentence (classicalNoZero (.constant 0 : Expr (Fin 0)))ᴺ ≠
      doubleNeg (neg (reflectedEquation (.constant 0 : Expr (Fin 0)))) := by
  rw [translated_classicalNoZero]
  intro h
  cases h

/-- A free variable outside the closure count remains a parameter. -/
theorem open_parameter_closure : Proves (.imp
    (Formula.closeN 2 (.eq (.var 7) (.var 0)))
    (Formula.closeN 2 (.eq (.var 0) (.var 7)))) := by
  apply closeN_imp 2
  apply Relative.imp_intro
  exact (relative_of_derives (.ass _ _ List.mem_cons_self)).eq_symm

theorem nested_closure {a : Formula} :
    Proves (.imp (Formula.closeN 3 (.all (.ex a)))
      (Formula.closeN 3 (.all (.ex a)))) :=
  closeN_imp 3 (relative_of_derives (Derives.identity [] _))

theorem zero_equation_comparison : Proves (.and
    (.imp (sentence (classicalNoZero (.constant 0 : Expr (Fin 0)))ᴺ)
      (ArithmeticExpression.noZeroSentence (.constant 0 : Expr (Fin 0))))
    (.imp (ArithmeticExpression.noZeroSentence (.constant 0 : Expr (Fin 0)))
      (sentence (classicalNoZero (.constant 0 : Expr (Fin 0)))ᴺ))) :=
  noZero_equivalence _

theorem fourteen_variable_comparison (e : Expr (Fin 14)) : Proves (.and
    (.imp (sentence (classicalNoZero e)ᴺ) (ArithmeticExpression.noZeroSentence e))
    (.imp (ArithmeticExpression.noZeroSentence e) (sentence (classicalNoZero e)ᴺ))) :=
  noZero_equivalence e

#print axioms reflectTerm_correct
#print axioms translatedTerm_correct
#print axioms binaryNumeral_correct
#print axioms expressionTerm_correct
#print axioms translated_classicalNoZero
#print axioms all_imp
#print axioms closeN_imp
#print axioms neg_eq_transport
#print axioms source_to_noZero
#print axioms noZero_to_source
#print axioms noZero_equivalence
#print axioms last_of_fourteen
#print axioms out_of_range_is_zero
#print axioms successor_is_add_one
#print axioms successor_not_definitional
#print axioms successor_proof
#print axioms odd_numeral_literal
#print axioms arbitrary_binary_proof
#print axioms separate_environments
#print axioms positive_input_literal
#print axioms zero_variable_GG
#print axioms two_variable_GG
#print axioms no_extra_GG_doubleNeg
#print axioms open_parameter_closure
#print axioms nested_closure
#print axioms zero_equation_comparison
#print axioms fourteen_variable_comparison
end DiophantineConsistency.FoundationHANoZeroChecks
