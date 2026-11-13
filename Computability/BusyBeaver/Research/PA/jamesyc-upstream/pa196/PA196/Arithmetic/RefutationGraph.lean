module
public import PA196.Arithmetic.Checker
@[expose] public section
namespace PA196.Arithmetic.RefutationGraph
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

noncomputable def formula : 𝚺ᴬ₁.Semisentence 1 :=
  Checker.verifyGraph.rew (Rew.subst ![‘2’,#0])

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem formula_graph (code : V) : formula.val.Evalb ![code] ↔ Checker.verifyValue code = 2 := by
  simp [formula,Checker.verify_graph,eq_comm]
#print axioms formula_graph
end PA196.Arithmetic.RefutationGraph
