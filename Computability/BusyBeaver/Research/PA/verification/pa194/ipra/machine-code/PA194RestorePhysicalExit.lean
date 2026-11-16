import PA194RestorePhysicalOrbit
import PA194Site31CodedFrame
import PA194Site32CodedZero
import PA194ModelLoopIteration

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace PA194RestorePhysicalExit
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion PA194ModelLoopIteration PA194ModelLoopState PA194ModelLoopFrame PA194ModelLoopCost PA194ModelSourceLoop PA194ActualSourceLoop PA194ActualLoopOrbit PA194ControllerLoopFrame PA194OneSpareReturn PA194StateOne PA194ZeroRuns PA194UnaryRuns PA194BinaryDouble PA194FiniteControls BinaryTapeCodes PackedDecoderModel TableDispatch PA194RegisterFile PA194RegisterPermutation PA194Path27Header
open PA194SourceSite25Physical
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem completeExit (r : Fin 9 → M) (tail k n spare : M) :
    let g := (((k+1)+1)+1)
    let r' := PA194ModelRestoreSource.running r (r 6)
    let k' := k+r 6
    let n' := n+r 6
    let e : Fin 13 → M := ![r' 0,r' 1,r' 2,r' 3,r' 4,r' 5,r' 6,r' 7,r' 8,tail,k'+1,n',spare]
    let args := PA194ActualLoopOrbit.frameArgs r' n' spare
    let output := PA194Site31OutputFile.updated args n'
    let x := packed g n spare (PA194ModelRestoreSource.source r tail)
    let orbitClock := F (timeCode (PA194ModelTransferState.next PA194ActualRestoreSource.triple)
      PA194RestorePhysicalCost.cost) ![r 6,x]
    F PA194Stepper.stepper ![F addCode ![F addCode ![orbitClock,F PA194Site31CodedClock.clockCode e],
        F PA194Site32ZeroClockCode.clockCode (Fin.cons k' output)],
      PA194SourceSite31Physical.physicalFrame 31 g (PA194ActualLoopOrbit.frameArgs r n spare)] =
      PA194SourceSite31Physical.physicalFrame 34 (((k'+1)+1)+1) output := by
  dsimp only
  let g := (((k+1)+1)+1)
  let r' := PA194ModelRestoreSource.running r (r 6)
  let k' := k+r 6
  let n' := n+r 6
  let e : Fin 13 → M := ![r' 0,r' 1,r' 2,r' 3,r' 4,r' 5,r' 6,r' 7,r' 8,tail,k'+1,n',spare]
  let args := PA194ActualLoopOrbit.frameArgs r' n' spare
  let output := PA194Site31OutputFile.updated args n'
  let x := packed g n spare (PA194ModelRestoreSource.source r tail)
  have heargs : PA194Site31SentenceClock.args e = args := by
    funext i
    fin_cases i <;> simp [args,e,PA194Site31SentenceClock.args,PA194Site31SentenceClock.regs,
      PA194ActualLoopOrbit.frameArgs,PA194ActualSourceLoop.args]
  have hz' : r' 6 = (0 : M) := by
    change F subCode ![r 6,r 6] = (0 : M)
    rw [modelSubAsTsub,tsub_self]
  have hz : output 6 = (0 : M) := by
    simpa [output,args,PA194Site31OutputFile.updated,PA194ActualLoopOrbit.frameArgs,PA194ActualSourceLoop.args] using hz'
  have ho := PA194RestorePhysicalOrbit.physicalOrbit r tail k n spare (r 6) (le_refl _)
  dsimp only at ho
  have hg : g+r 6 = (((k'+1)+1)+1) := by dsimp [g,k']; simp [add_assoc,add_comm,add_left_comm]
  rw [hg] at ho
  have h31 := PA194Site31CodedFrame.frameStep e
  dsimp only at h31
  change F PA194Stepper.stepper ![F PA194Site31CodedClock.clockCode e,
      PA194SourceSite31Physical.physicalFrame 31 (((k'+1)+1)+1) (PA194Site31SentenceClock.args e)] =
    PA194SourceSite31Physical.physicalFrame 32 ((k'+1)+1)
      (PA194Site31OutputFile.updated (PA194Site31SentenceClock.args e) n') at h31
  rw [heargs] at h31
  have h32 := PA194Site32CodedZero.zeroPath k' output hz
  rw [PA194StepperCompose.modelStepperCompose,PA194StepperCompose.modelStepperCompose,ho,h31,h32]
#print axioms completeExit
end models
end PA194RestorePhysicalExit
