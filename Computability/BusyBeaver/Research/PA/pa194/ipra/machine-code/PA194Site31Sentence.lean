import PA194Site31SentenceFrame
import PA194Site31PhysicalClock
import PA194ActualLoopOrbit
import PA194ModelLoopFrameAt
import PA194StartupSentence
import PRAEqualityToIPRA
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
noncomputable section
namespace PA194Site31Sentence
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open PRAModelIOpenPairing PRAExhaustion PA194ModelLoopIteration PA194ModelLoopState PA194ModelLoopFrame PA194ModelLoopFrameAt PA194ControllerLoopFrame PA194OneSpareReturn PA194StateOne PA194ZeroRuns PA194UnaryRuns PA194BinaryDouble PA194FiniteControls BinaryTapeCodes PackedDecoderModel TableDispatch PA194RegisterFile PA194RegisterPermutation PA194Path27Header PA194StartupSentence
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem modelSentence : M↓[language] ⊧ sentence := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  apply (eqClosureModels _ _).mpr
  intro e
  let args := PA194Site31SentenceClock.args e
  let newArgs := PA194Site31OutputFile.updated args (e 11)
  have ht : args 10 = F repeatOutput ![e 11,(0 : M)] := by simp [args,PA194Site31SentenceClock.args,PA194ActualLoopOrbit.frameArgs]
  have hs : physicalArgs args 10 = F repeatOutput ![e 11,(0 : M)] := by simpa only [sourceSuffixAt] using ht
  have hn : newArgs 10 = F repeatOutput ![F Code.succ (fun _ => e 11),(0 : M)] := by simp [newArgs,PA194Site31OutputFile.updated]
  have hin := frameSourceAt 31 args ((e 10+1)+1) (e 11) (e 9) ht
  have hout := frameSourceAt 32 newArgs (e 10+1) (F Code.succ (fun _ => e 11)) (e 9) hn
  have step := PA194Site31PhysicalClock.frameStep (e 10) (e 11) args hs
  change _ = PA194SourceSite31Physical.physicalFrame 31 ((e 10+1)+1) args at hin
  change _ = PA194SourceSite31Physical.physicalFrame 32 (e 10+1) newArgs at hout
  rw [←hin,←hout] at step
  have valFrame (site : Nat) (t : T) :
      Semiterm.val e Empty.elim (frame site t) =
        F (frameAt site readers) (fun _ => Semiterm.val e Empty.elim t) := by
    simp only [frame,Semiterm.val_func]
    congr 1
    funext i
    fin_cases i <;> rfl
  change Semiterm.val e Empty.elim (afterT (run clock24 (frame 31 input))) =
    Semiterm.val e Empty.elim (frame 32 output)
  rw [PA194Site31SentenceRun.valAfter]
  simp only [run, PA194StartupSentence.valApp2, valFrame,
    PA194Site31SentenceClock.valClock, PA194Site31SentenceFrame.valInput,
    PA194Site31SentenceFrame.valOutput]
  exact step
end models
theorem classicalPRA : PRA ⊢ sentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelSentence
theorem nativeIPRA : standardTheory ⊢ equalClosureI lhs rhs := nativeOfClassical lhs rhs classicalPRA
#print axioms modelSentence
#print axioms classicalPRA
#print axioms nativeIPRA
end PA194Site31Sentence
