module
public import M6PA.Theory
public import M6PA.Scheduler.ActualRefutationGraph
@[expose] public section
namespace M6.PA.InternalActualRefutation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
noncomputable def noActualRefutationSentence : ArithmeticSentence :=
  “∀ code, ¬!ActualRefutationGraph.formula code”
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
theorem noActualRefutation_correct :
    (V ⊧/![] noActualRefutationSentence) ↔
      ∀ code : V,ActualCheckerBlueprint.verifyValue code≠2 := by
  simp [noActualRefutationSentence,ActualRefutationGraph.formula_graph]
end M6.PA.InternalActualRefutation
