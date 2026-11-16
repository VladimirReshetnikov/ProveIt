import PA194RestorePhysicalExit
import PA194RestorePhysicalFrameAny
import PA194ModelLoopIteration

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace PA194RestorePhysicalExitCode
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
    let r'' := Function.update r' 0 (r' 0+1)
    let k' := k+r 6
    let n' := n+r 6
    let e : Fin 13 → M := ![r' 0,r' 1,r' 2,r' 3,r' 4,r' 5,r' 6,r' 7,r' 8,tail,k'+1,n',spare]
    let args := PA194ActualLoopOrbit.frameArgs r' n' spare
    let output := PA194Site31OutputFile.updated args n'
    let x := packed g n spare (PA194ModelRestoreSource.source r tail)
    let y := packed (g+r 6) (n'+1) spare (PA194ModelRestoreSource.source r'' tail)
    let orbitClock := F (timeCode (PA194ModelTransferState.next PA194ActualRestoreSource.triple)
      PA194RestorePhysicalCost.cost) ![r 6,x]
    F PA194Stepper.stepper ![F addCode ![F addCode ![orbitClock,F PA194Site31CodedClock.clockCode e],
      F PA194Site32ZeroClockCode.clockCode (Fin.cons k' output)],
      F (PA194ModelLoopFrameAt.frameAt 31 readers) (fun _ => x)] =
      F (PA194ModelLoopFrameAt.frameAt 34 readers) (fun _ => y) := by
  let g := (((k+1)+1)+1)
  let r' := PA194ModelRestoreSource.running r (r 6)
  let r'' := Function.update r' 0 (r' 0+1)
  let k' := k+r 6
  let n' := n+r 6
  let args := PA194ActualLoopOrbit.frameArgs r' n' spare
  let output := PA194Site31OutputFile.updated args n'
  have hout : output = PA194ActualLoopOrbit.frameArgs r'' (n'+1) spare := by
    funext i
    fin_cases i <;> simp [output,args,r'',PA194Site31OutputFile.updated,PA194ActualLoopOrbit.frameArgs,
      PA194ActualSourceLoop.args,←modelAddOne] <;> rfl
  have hg : g+r 6 = (((k'+1)+1)+1) := by dsimp [g,k']; simp [add_assoc,add_comm,add_left_comm]
  have hf := PA194RestorePhysicalFrameAny.frameSource 31 r tail g n spare
  have hf' := PA194RestorePhysicalFrameAny.frameSource 34 r'' tail (g+r 6) (n'+1) spare
  have hp := PA194RestorePhysicalExit.completeExit r tail k n spare
  dsimp only at hp ⊢
  dsimp only [output,args,r'',n'] at hout
  dsimp only [g,k'] at hg
  dsimp only [g] at hf
  dsimp only [g,r'',n'] at hf'
  rw [hout,←hg,←hf,←hf'] at hp
  rw [hout]
  exact hp
#print axioms completeExit
end models
end PA194RestorePhysicalExitCode
