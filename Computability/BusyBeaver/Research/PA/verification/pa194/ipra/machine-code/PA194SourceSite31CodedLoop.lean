import PA194Site31CodedFrame
import PA194Site32CodedPositive
import PA194Site31PhysicalClock
import PA194SourceSite32PositivePhysical
import PA194SourceSite33Physical
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194SourceSite31CodedLoop
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194Site31SentenceClock PA194SourceSite31Controller PA194SourceSite31Physical PA194SourceControllerCode TableDispatch PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble PA194FiniteControls BinaryTapeCodes PRAModelIOpenPairing PA194Path27Header
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem oneLoop (e : Fin 13 → M) (k m : M) (hgap : e 10 = k+1) (hm : e 6 = m+1) :
    let args := PA194Site31SentenceClock.args e
    let first := PA194Site31OutputFile.updated args (e 11)
    let output := Function.update first 6 m
    F step ![F step ![F step ![sourceState 31 args (e 9)]]] = sourceState 31 output (e 9) ∧
    F PA194Stepper.stepper ![F addCode ![F addCode ![F PA194Site31CodedClock.clockCode e,
        F PA194Site32PositiveClockCode.clockCode (Fin.cons k first)],modelNumeral M 34],
      physicalFrame 31 (((k+1)+1)+1) args] =
        physicalFrame 31 ((((k+1)+1)+1)+1) output := by
  dsimp only
  let args := PA194Site31SentenceClock.args e
  let first := PA194Site31OutputFile.updated args (e 11)
  let output := Function.update first 6 m
  have h6 : args 6 = m+1 := by simpa [args,PA194Site31SentenceClock.args,PA194ActualLoopOrbit.frameArgs,PA194ActualSourceLoop.args,PA194Site31SentenceClock.regs] using hm
  have hm' : first 6 = m+1 := by simpa [first,PA194Site31OutputFile.updated] using h6
  have hs31 := PA194SourceSite31Controller.controllerStep args (e 9) (F PA194OneSpareReturn.repeatOutput ![F Code.succ (fun _ => e 11),(0 : M)])
  change F step ![sourceState 31 args (e 9)] = sourceState 32 first (e 9) at hs31
  have hp31 := PA194Site31CodedFrame.frameStep e
  dsimp only at hp31
  rw [hgap] at hp31
  have h32 := PA194SourceSite32PositivePhysical.positiveBranch k (e 9) m first hm'
  obtain ⟨hs32,clock,hp32⟩ := h32
  have hp32' := PA194Site32CodedPositive.positivePath k m first hm'
  have h33 := PA194SourceSite33Physical.sourcePhysical (k+1) (e 9) output
  obtain ⟨hs33,hp33⟩ := h33
  constructor
  · rw [hs31,hs32,hs33]
  · rw [PA194StepperCompose.modelStepperCompose,PA194StepperCompose.modelStepperCompose,hp31,hp32',hp33]
#print axioms oneLoop
end models
end PA194SourceSite31CodedLoop
