module
public import PA196.Arithmetic.RefutationGraph
public import M6PA.Theory
@[expose] public section

namespace PA196.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

/-- The PA196 numeric checker accepts no refutation certificate. -/
noncomputable def noRefutationSentence : ArithmeticSentence :=
  “∀ code, ¬!RefutationGraph.formula code”

theorem noRefutation_correct {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* M6.PA.theory] :
    (V ⊧/![] noRefutationSentence) ↔ ∀ code : V, Checker.verifyValue code≠2 := by
  simp [noRefutationSentence,RefutationGraph.formula_graph]

end PA196.Arithmetic
