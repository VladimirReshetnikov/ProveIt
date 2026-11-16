module
public import PA196.Arithmetic.Realizes
@[expose] public section
namespace PA196.Arithmetic.CommandStep
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open CommandWord

/-- Exact clean live-state graph; zero remains a distinct halted code. -/
noncomputable def cleanStateGraph : 𝚺ᴬ₁.Semisentence 3 :=
  .mkSigma “z t w. ∃ x y r, !adjoinDef x 0 0 ∧ !adjoinDef y 0 x ∧
    !adjoinDef r w y ∧ !adjoinDef z t r”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem cleanState_graph (z t w : V) :
    cleanStateGraph.val.Evalb ![z,t,w] ↔ z=stateCode t w 0 0 := by
  simp [cleanStateGraph,stateCode]

/-- Unrestricted arithmetic formula: no claim that the universal clean-state
invariant is Sigma-one or eligible for only Sigma-one induction. -/
noncomputable def realizesFormula : ArithmeticSemisentence 2 :=
  “word a. ∀ t w, ∃ initial target,
    !cleanStateGraph initial t w ∧ !cleanStateGraph target a w ∧
    (!wordGraph 0 word initial ∨ !wordGraph target word initial)”

theorem realizes_formula (word a : V) :
    realizesFormula.Evalb ![word,a] ↔ Realizes word a := by
  simp [realizesFormula,cleanState_graph,word_graph,Realizes,eq_comm]

#print axioms cleanState_graph
#print axioms realizes_formula
end PA196.Arithmetic.CommandStep

