module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import PA196.Arithmetic.CompilerInvariant
public import PA196.Arithmetic.RefutationGraph
@[expose] public section
open M6.Arithmetic.PA
namespace PA196.Arithmetic.CompilerHaltingWord
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open CommandStep CommandWord Compiler
open CompilerSoundness LiteralWords
open M6.PA.SourceCantorInternal
open VectorAppend
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def resetAtom : Nat := Commands.atom (.ax 0 0 0)
def shiftAtom : Nat := 0

theorem concat_eq_append_singleton (xs x : V) : concat xs x=append xs (x∷0) := by
  induction xs using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => simp
  case adjoin y ys ih => simp [ih]

noncomputable def haltWord (code : V) : V :=
  (resetAtom : V) ∷ concat (compiledValue code) (shiftAtom : V)
noncomputable def haltWordGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “word code. ∃ compiled suffix, !compiledGraph compiled code ∧
    !concatDef suffix compiled ↑shiftAtom ∧ !adjoinDef word ↑resetAtom suffix”
theorem haltWord_graph (word code : V) : haltWordGraph.val.Evalb ![word,code] ↔ word=haltWord code := by
  simp [haltWordGraph,compiled_graph,haltWord,numeral_eq_natCast]

noncomputable def liveStateGraph : 𝚺ᴬ₁.Semisentence 5 := .mkSigma
  “z t w d h. ∃ x y r, !adjoinDef x h 0 ∧ !adjoinDef y d x ∧
    !adjoinDef r w y ∧ !adjoinDef z t r”
theorem liveState_graph (z t w d h : V) :
    liveStateGraph.val.Evalb ![z,t,w,d,h] ↔ z=stateCode t w d h := by
  simp [liveStateGraph,stateCode]

section Peano
variable [V↓[ℒₒᵣ] ⊧* theory]
/-- The exact reset/compiled/shift word halts from every live four-register
command state, including dirty caches, in every PA model. -/
theorem refutation_word_halts (code t w d h : V)
    (hc : Checker.verifyValue code=2) :
    wordValue (haltWord code) (stateCode t w d h)=0 := by
  have hcode : Checker.verifyValue code=(1:V)+1 := by simpa only [one_add_one_eq_two] using hc
  have hr := accepted_compiler_realizes code 1 hcode
  have ha : (resetAtom : V)=axCode 0 0 0 := by
    simpa only [resetAtom,Nat.cast_zero] using ax_atom_numeral (V:=V) 0 0 0
  have hs : (shiftAtom : V)=0 := by rfl
  rw [haltWord,concat_eq_append_singleton,word_cons,ha,ax_value,word_append,
    word_cons,word_zero,hs]
  rcases hr (gateValue (h+0) (d+0) 0 d)
    ((schemaHeads (d+0) (h+0) 0 d h ++ [t]).foldr pairValue w) with he | he
  · rw [he,step_halted]
  · rw [he,shift_value]
    simp
end Peano
noncomputable def refutationHaltsSentence : ArithmeticSentence :=
  “∀ code, !RefutationGraph.formula code → ∀ t w d h, ∃ word state,
    !haltWordGraph word code ∧ !liveStateGraph state t w d h ∧ !wordGraph 0 word state”

/-- Actual PA proves the explicit refutation-to-arithmetic-word halting
implication. This sentence makes no source or physical trace assertion. -/
theorem pa_proves_refutation_word_halts : theory ⊢ refutationHaltsSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [refutationHaltsSentence,models_iff]
  simp [RefutationGraph.formula_graph,haltWord_graph,liveState_graph,word_graph,
    eq_comm,Matrix.comp_vecCons'']
  intro code hc t w d h
  exact (refutation_word_halts code t w d h hc.symm).symm

#print axioms pa_proves_refutation_word_halts
#print axioms refutation_word_halts
end PA196.Arithmetic.CompilerHaltingWord

