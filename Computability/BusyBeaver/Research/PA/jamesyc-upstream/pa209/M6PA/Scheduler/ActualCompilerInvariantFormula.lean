module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualCompilerRuleSoundness
public import M6PA.Scheduler.ActualCompilerBlueprint
public import M6PA.Scheduler.ActualCheckerBlueprint
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.ActualCompilerLeafSoundness
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCommandStepGraph

noncomputable def tableRealizesFormula : ArithmeticSemisentence 2 :=
  “previous words. ∀ i a word, (!nthDef (a+1) previous i ∧ !nthDef word words i) →
    !realizesFormula word a”
noncomputable def fuelInvariantFormula : ArithmeticSemisentence 1 :=
  “fuel. ∀ bound, ∃ previous words,
    !ActualCheckerBlueprint.tableGraph previous fuel bound ∧
    !ActualCompilerBlueprint.tableGraph words fuel bound ∧ !tableRealizesFormula previous words”
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem tableRealizes_formula (previous words : V) :
    tableRealizesFormula.Evalb ![previous,words] ↔ TableRealizes previous words := by
  simp [tableRealizesFormula,realizes_formula,TableRealizes,eq_comm]
theorem fuelInvariant_formula (fuel : V) :
    fuelInvariantFormula.Evalb ![fuel] ↔ ∀ bound : V,
      TableRealizes (ActualCheckerBlueprint.tableValue fuel bound)
        (ActualCompilerBlueprint.tableValue fuel bound) := by
  simp [fuelInvariantFormula,ActualCheckerBlueprint.table_graph,
    ActualCompilerBlueprint.table_graph,tableRealizes_formula]
#print axioms tableRealizes_formula
#print axioms fuelInvariant_formula
end M6.PA.ActualCompilerLeafSoundness

