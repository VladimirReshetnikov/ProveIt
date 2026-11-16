import PA194Site31CodedClock
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
namespace PA194Site31CodedFrame
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open PA194Site31Sentence PA194Site31SentenceClock PA194Site31SentenceFrame PA194ModelLoopFrameAt PA194ControllerLoopFrame
open PRAModelIOpenPairing PRAExhaustion PA194ModelLoopIteration PA194ModelLoopState PA194ModelLoopFrame PA194ModelLoopFrameAt PA194ControllerLoopFrame PA194OneSpareReturn PA194StateOne PA194ZeroRuns PA194UnaryRuns PA194BinaryDouble PA194FiniteControls BinaryTapeCodes PackedDecoderModel TableDispatch PA194RegisterFile PA194RegisterPermutation PA194Path27Header PA194StartupSentence
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem frameStep (e : Fin 13 → M) :
    let args := PA194Site31SentenceClock.args e
    let updated := PA194Site31OutputFile.updated args (e 11)
    F PA194Stepper.stepper ![F PA194Site31CodedClock.clockCode e,
      PA194SourceSite31Physical.physicalFrame 31 ((e 10+1)+1) args] =
      PA194SourceSite31Physical.physicalFrame 32 (e 10+1) updated := by
  dsimp only
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let args := PA194Site31SentenceClock.args e
  let newArgs := PA194Site31OutputFile.updated args (e 11)
  have ht : args 10 = F repeatOutput ![e 11,(0 : M)] := by simp [args,PA194Site31SentenceClock.args,PA194ActualLoopOrbit.frameArgs]
  have hn : newArgs 10 = F repeatOutput ![F Code.succ (fun _ => e 11),(0 : M)] := by simp [newArgs,PA194Site31OutputFile.updated]
  have hin := frameSourceAt 31 args ((e 10+1)+1) (e 11) (e 9) ht
  have hout := frameSourceAt 32 newArgs (e 10+1) (F Code.succ (fun _ => e 11)) (e 9) hn
  change _ = PA194SourceSite31Physical.physicalFrame 31 ((e 10+1)+1) args at hin
  change _ = PA194SourceSite31Physical.physicalFrame 32 (e 10+1) newArgs at hout
  have valFrame (site : Nat) (t : T) :
      Semiterm.val e Empty.elim (PA194Site31Sentence.frame site t) =
        F (frameAt site readers) (fun _ => Semiterm.val e Empty.elim t) := by
    simp only [PA194Site31Sentence.frame,Semiterm.val_func]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hspare : args 9 = e 12 := by simp [args,PA194Site31SentenceClock.args,PA194ActualLoopOrbit.frameArgs]
  rw [hspare] at hin
  have h := PA194Site31CodedClock.codedFrame e
  simp only [valFrame,PA194Site31SentenceFrame.valInput,PA194Site31SentenceFrame.valOutput] at h
  rw [hin,hout] at h
  exact h
#print axioms frameStep
end models
end PA194Site31CodedFrame
