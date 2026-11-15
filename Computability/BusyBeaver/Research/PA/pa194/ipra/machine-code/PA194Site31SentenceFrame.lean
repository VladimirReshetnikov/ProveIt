import PA194Site31SentenceRun
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
namespace PA194Site31SentenceFrame
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194StateOne PA194UnaryRuns PA194BinaryDouble PA194FiniteControls PA194RegisterFile PA194RegisterPermutation PA194StartupSentence PA194Site31Sentence PA194Site31SentenceVectors PA194Site31SentenceClock PA194ControllerLoopFrame
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem valInput (e : Fin 13 → M) :
    Semiterm.val e Empty.elim input = PA194ModelLoopState.packed ((e 10+1)+1) (e 11) (e 12) (source (args e) (e 9)) := by
  have hsrc := PA194ActualLoopOrbit.controllerSource (regs e) (e 11) (e 12) (e 9)
  change source (args e) (e 9) = PA194ModelSourceLoop.source (regs e) (e 9) at hsrc
  rw [hsrc]
  simp [input,packedT,sourceT,P,A,plus1,R,tail,k,count,PA194Site31Sentence.spare,
    PA194StartupSentence.valApp2,PA194StartupSentence.valState,PA194StartupSentence.valOne,
    Semiterm.val_bvar,PA194ModelLoopState.packed,PA194ModelSourceLoop.source,regs,modelPairCode]
  rfl

theorem valOutput (e : Fin 13 → M) :
    let newArgs := PA194Site31OutputFile.updated (args e) (e 11)
    Semiterm.val e Empty.elim output = PA194ModelLoopState.packed (e 10+1) (F Code.succ (fun _ => e 11)) (newArgs 9) (source newArgs (e 9)) := by
  dsimp only
  let newArgs := PA194Site31OutputFile.updated (args e) (e 11)
  have hspare : newArgs 9 = e 12 := by simp [newArgs,PA194Site31OutputFile.updated,args,PA194ActualLoopOrbit.frameArgs]
  have hregs : PA194ControllerLoopFrame.regsOfArgs newArgs = Function.update (regs e) 0 ((regs e) 0+1) := by
    funext i
    fin_cases i <;> simp [newArgs,PA194Site31OutputFile.updated,args,PA194ActualLoopOrbit.frameArgs,
      PA194ActualSourceLoop.args,PA194ControllerLoopFrame.regsOfArgs,regs]
  have hsrc : source newArgs (e 9) = PA194ModelSourceLoop.source (Function.update (regs e) 0 ((regs e) 0+1)) (e 9) := by
    simp only [PA194ControllerLoopFrame.source,PA194ModelSourceLoop.source]
    rw [hregs]
    rfl
  change _ = PA194ModelLoopState.packed (e 10+1) (F Code.succ (fun _ => e 11)) (newArgs 9) (source newArgs (e 9))
  rw [hspare,hsrc,←modelAddOne]
  simp [output,packedT,sourceT,sourceOut,P,A,plus1,R,tail,k,count,PA194Site31Sentence.spare,
    PA194StartupSentence.valApp2,PA194StartupSentence.valState,PA194StartupSentence.valOne,
    Semiterm.val_bvar,PA194ModelLoopState.packed,PA194ModelSourceLoop.source,regs,Function.update,modelPairCode]
  exact ⟨rfl, rfl, rfl⟩
#print axioms valInput
#print axioms valOutput
end models
end PA194Site31SentenceFrame
