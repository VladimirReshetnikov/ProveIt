module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualCompilerStandard
public import M6PA.Scheduler.ActualWordEncodingBlueprint
public import M6PA.Scheduler.ActualCodeCompilerWord
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.ActualCandidateBlueprint
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCompilerBlueprint ActualWordEncodingBlueprint
attribute [local irreducible] compiledGraph encodeGraph

def resetAtom : Nat := M6.Source.CommandAtomEncoding.atom (.ax 0 0 0)
def shiftAtom : Nat := M6.Source.CommandAtomEncoding.atom .shift

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def candidateValue (code : V) : V :=
  encodeValue ((resetAtom : V) ∷ concat (compiledValue code) (shiftAtom : V))-1

/-- Fixed explicit graph of the V1 certificate-to-enumeration-candidate
compiler, not a chosen computable-function representation. -/
noncomputable def candidateGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “z code. ∃ word suffix full encoded,
    !compiledGraph word code ∧ !concatDef suffix word ↑shiftAtom ∧
    !adjoinDef full ↑resetAtom suffix ∧ !encodeGraph encoded full ∧ !subDef z encoded 1”

theorem candidate_graph (z code : V) : candidateGraph.val.Evalb ![z,code] ↔ z=candidateValue code := by
  simp [candidateGraph,compiled_graph,encode_graph,candidateValue,numeral_eq_natCast,Matrix.comp_vecCons'']

theorem candidate_total_unique (code : V) : ∃! z,candidateGraph.val.Evalb ![z,code] :=
  ⟨candidateValue code,(candidate_graph _ _).mpr rfl,fun _ hz => (candidate_graph _ _).mp hz⟩

open ActualCompilerStandard ActualWordCoding NativeCalculus.ActualBasis.Code
open M6.Source.CommandAtomEncoding

theorem candidate_standard (code : Nat) : candidateValue code=candidateCode code := by
  unfold candidateValue
  rw [compiled_standard]
  rw [← encode_concat,← encode_cons,encode_standard]
  rw [ActualWordMacros.sub_standard,compiledAtoms_eq]
  simp only [candidateCode,haltCertificate,atoms,List.map_append,List.map_cons,List.map_nil,
    List.singleton_append,resetAtom,shiftAtom]
  all_goals rfl

noncomputable def totalSentence : ArithmeticSentence := “∀ code, ∃ z, !candidateGraph z code”
theorem pa_proves_candidate_total : theory ⊢ totalSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp [totalSentence,models_iff,candidate_graph]

#print axioms candidate_graph
#print axioms candidate_standard
#print axioms pa_proves_candidate_total
end M6.PA.ActualCandidateBlueprint

