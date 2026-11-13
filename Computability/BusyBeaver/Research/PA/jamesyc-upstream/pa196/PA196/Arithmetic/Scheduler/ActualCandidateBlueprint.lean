module
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Compiler
public import PA196.Arithmetic.Scheduler.ActualWordEncodingBlueprint
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Scheduler.ActualCandidateBlueprint
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open Compiler ActualWordEncodingBlueprint
attribute [local irreducible] compiledGraph encodeGraph

def resetAtom : Nat := PA196.Commands.atom (.ax 0 0 0)
def shiftAtom : Nat := PA196.Commands.atom .shift

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def candidateValue (code : V) : V :=
  encodeValue ((resetAtom : V) ∷ concat (compiledValue code) (shiftAtom : V))-1

/-- Fixed explicit graph of the PA196 certificate-to-enumeration-candidate
compiler, not a chosen computable-function representation. -/
noncomputable def candidateGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “z code. ∃ word suffix full encoded,
    !compiledGraph word code ∧ !concatDef suffix word ↑shiftAtom ∧
    !adjoinDef full ↑resetAtom suffix ∧ !encodeGraph encoded full ∧ !subDef z encoded 1”

theorem candidate_graph (z code : V) : candidateGraph.val.Evalb ![z,code] ↔ z=candidateValue code := by
  simp [candidateGraph,compiled_graph,encode_graph,candidateValue,numeral_eq_natCast,Matrix.comp_vecCons'']

theorem candidate_total_unique (code : V) : ∃! z,candidateGraph.val.Evalb ![z,code] :=
  ⟨candidateValue code,(candidate_graph _ _).mpr rfl,fun _ hz => (candidate_graph _ _).mp hz⟩

noncomputable def totalSentence : ArithmeticSentence := “∀ code, ∃ z, !candidateGraph z code”
theorem pa_proves_candidate_total : PA196.Arithmetic.Machine.PA.theory ⊢ totalSentence := by
  apply Arithmetic.complete.{0} PA196.Arithmetic.Machine.PA.theory _
  intro V _ _
  simp [totalSentence,models_iff,candidate_graph]

#print axioms candidate_graph
#print axioms pa_proves_candidate_total
end PA196.Arithmetic.Scheduler.ActualCandidateBlueprint

