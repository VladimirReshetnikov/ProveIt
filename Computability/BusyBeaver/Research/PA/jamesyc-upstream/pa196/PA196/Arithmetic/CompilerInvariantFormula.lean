module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import PA196.Arithmetic.CompilerRuleSoundness
public import PA196.Arithmetic.Compiler
public import PA196.Arithmetic.Checker
@[expose] public section
open M6.Arithmetic.PA
namespace PA196.Arithmetic.CompilerSoundness
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open CommandStep

noncomputable def tableRealizesFormula : ArithmeticSemisentence 2 :=
  “previous words. ∀ i a word, (!nthDef (a+1) previous i ∧ !nthDef word words i) →
    !realizesFormula word a”
noncomputable def fuelInvariantFormula : ArithmeticSemisentence 1 :=
  “fuel. ∀ bound, ∃ previous words,
    !Checker.tableGraph previous fuel bound ∧
    !Compiler.tableGraph words fuel bound ∧ !tableRealizesFormula previous words”
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem tableRealizes_formula (previous words : V) :
    tableRealizesFormula.Evalb ![previous,words] ↔ TableRealizes previous words := by
  simp [tableRealizesFormula,realizes_formula,TableRealizes,eq_comm]
theorem fuelInvariant_formula (fuel : V) :
    fuelInvariantFormula.Evalb ![fuel] ↔ ∀ bound : V,
      TableRealizes (Checker.tableValue fuel bound)
        (Compiler.tableValue fuel bound) := by
  simp [fuelInvariantFormula,Checker.table_graph,
    Compiler.table_graph,tableRealizes_formula]
#print axioms tableRealizes_formula
#print axioms fuelInvariant_formula
end PA196.Arithmetic.CompilerSoundness

