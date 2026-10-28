import DiophantineConsistency.FoundationHACurrentNoZero2011

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHACurrentNoZero2011Checks
open LO LO.FirstOrder
open scoped LO.FirstOrder
open SetTheory.PA HA FoundationPAHFSyntax FoundationHANoZero
open FoundationHACurrentNoZero2011 ObjectCurrentEquation2011
attribute [local irreducible] expression naturalExpression

/-- Same old port names, complete finite kernel, and one high-port shift. -/
theorem beta_port : CurrentWindowCarry2011.ports 0 = (CurrentMasks2011.beta : ℤ) := rfl
theorem kernel_port : CurrentWindowCarry2011.ports 1 = (CurrentKernel2011.K : ℤ) := rfl
theorem low_port : CurrentWindowCarry2011.ports 2 = (CurrentMasks2011.lowPort : ℤ) := rfl
theorem high_port : CurrentWindowCarry2011.ports 3 =
    ((CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ) : ℤ) := rfl

theorem fixed_width : CurrentMasks2011.width = 94517 := rfl

theorem exact_support : CurrentMasks2011.lowSupport =
    Finset.range 951 ∪ Finset.Ico 960 986 ∪ {1004} := CurrentMasks2011.lowSupport_def

theorem single_positive_shift : naturalExpression =
    (expressionAt CurrentWindowCarry2011.ports).subst
      (fun i => Expr.var i + Expr.constant 1) := by
  simp only [naturalExpression, expression, positiveShift]

theorem exact_closed_target : ArithmeticCurrentEquation2011.unsolvabilitySentence =
    Formula.closeN 14 (.imp (ArithmeticExpression.equation naturalExpression Fin.val) .bot) := rfl

theorem actual_sentence : Formula.Sentence ArithmeticCurrentEquation2011.unsolvabilitySentence :=
  ArithmeticExpression.sentence_noZeroSentence naturalExpression

theorem actual_HA_comparison : Proves (.and
    (.imp (sentence classicalSentenceᴺ) ArithmeticCurrentEquation2011.unsolvabilitySentence)
    (.imp ArithmeticCurrentEquation2011.unsolvabilitySentence (sentence classicalSentenceᴺ))) :=
  current_equivalence

#print axioms WangTiles942.row_indices_exact
#print axioms WangTiles942.ordered_count
#print axioms current_syntax
#print axioms translated_source
#print axioms source_to_current
#print axioms current_to_source
#print axioms current_equivalence
#print axioms proof_exists_iff
#print axioms beta_port
#print axioms kernel_port
#print axioms low_port
#print axioms high_port
#print axioms fixed_width
#print axioms exact_support
#print axioms single_positive_shift
#print axioms exact_closed_target
#print axioms actual_sentence
#print axioms actual_HA_comparison
end DiophantineConsistency.FoundationHACurrentNoZero2011Checks
