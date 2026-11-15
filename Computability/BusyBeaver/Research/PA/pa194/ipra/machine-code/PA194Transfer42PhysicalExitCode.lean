import PA194Transfer42PhysicalExit
import PA194Transfer42ExitFrame
import PA194ModelLoopIteration

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace PA194Transfer42PhysicalExitCode
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
    let g := (k+1)+1
    let r' := PA194ModelTransfer42Source.running r (r 7)
    let n' := n+r 7
    let x := packed g n spare (PA194ModelTransfer42Source.source r tail)
    let y0 := packed (g+r 7) n' spare (PA194ModelTransfer42Source.source r' tail)
    let y := packed ((g+r 7)+1) n' spare (PA194ModelTransfer42Source.source r' tail)
    let orbitClock := F (timeCode (PA194ModelTransferState.next PA194ActualTransfer42Source.triple)
      PA194Transfer42PhysicalCost.cost) ![r 7,x]
    F PA194Stepper.stepper ![F addCode ![orbitClock,F PA194Transfer42PhysicalZeroCost.cost (fun _ => y0)],
      F (PA194ModelLoopFrameAt.frameAt 42 readers) (fun _ => x)] =
      F (PA194ModelLoopFrameAt.frameAt 45 readers) (fun _ => y) := by
  let g := (k+1)+1
  let r' := PA194ModelTransfer42Source.running r (r 7)
  let k' := k+r 7
  let n' := n+r 7
  have hg : g+r 7 = (k'+1)+1 := by dsimp [g,k']; simp [add_assoc,add_comm,add_left_comm]
  have hf := PA194Transfer42PhysicalFrame.frameSource r tail g n spare
  have hf' := PA194Transfer42ExitFrame.frameSource r' tail ((g+r 7)+1) n' spare
  have hp := PA194Transfer42PhysicalExit.completeExit r tail k n spare
  dsimp only at hp ⊢
  dsimp only [g,k'] at hg
  dsimp only [g] at hf
  dsimp only [g,n'] at hf'
  rw [←hg,←hf,←hf'] at hp
  exact hp
#print axioms completeExit
end models
end PA194Transfer42PhysicalExitCode
