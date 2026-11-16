import PA194Transfer45PhysicalOrbit
import PA194Site45ZeroClockCode
import PA194Transfer45PhysicalZeroCost
import PA194ModelLoopIteration

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace PA194Transfer45PhysicalExit
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
    let r' := PA194ModelTransfer45Source.running r (r 6)
    let k' := k+r 6
    let n' := n+r 6
    let args := PA194ActualLoopOrbit.frameArgs r' n' spare
    let x := packed g n spare (PA194ModelTransfer45Source.source r tail)
    let y := packed (((k'+1)+1)) n' spare (PA194ModelTransfer45Source.source r' tail)
    let orbitClock := F (timeCode (PA194ModelTransferState.next PA194ActualTransfer45Source.triple)
      PA194Transfer45PhysicalCost.cost) ![r 6,x]
    F PA194Stepper.stepper ![F addCode ![orbitClock,F PA194Transfer45PhysicalZeroCost.cost (fun _ => y)],
      PA194SourceSite31Physical.physicalFrame 45 g (PA194ActualLoopOrbit.frameArgs r n spare)] =
      PA194SourceSite31Physical.physicalFrame 48 (((k'+1)+1)+1) args := by
  dsimp only
  let g := (k+1)+1
  let r' := PA194ModelTransfer45Source.running r (r 6)
  let k' := k+r 6
  let n' := n+r 6
  let args := PA194ActualLoopOrbit.frameArgs r' n' spare
  let x := packed g n spare (PA194ModelTransfer45Source.source r tail)
  let y := packed ((k'+1)+1) n' spare (PA194ModelTransfer45Source.source r' tail)
  have hz' : r' 6 = (0 : M) := by
    change F subCode ![r 6,r 6] = (0 : M)
    rw [modelSubAsTsub,tsub_self]
  have hz : args 6 = (0 : M) := by
    simpa [args,PA194ActualLoopOrbit.frameArgs,PA194ActualSourceLoop.args] using hz'
  have ho := PA194Transfer45PhysicalOrbit.physicalOrbit r tail k n spare (r 6) (le_refl _)
  dsimp only at ho
  have hg : g+r 6 = (k'+1)+1 := by dsimp [g,k']; simp [add_assoc,add_comm,add_left_comm]
  rw [hg] at ho
  have hzero := PA194Site45ZeroClockExact.exactClock k' args hz
  have hcode := PA194Site45ZeroClockCode.modelClock (Fin.cons k' args)
  change F PA194Site45ZeroClockCode.clockCode (Fin.cons k' args) = PA194Site45ZeroClockExact.clock k' args at hcode
  have hcost := PA194Transfer45PhysicalZeroCost.modelCost r' tail k' n' spare
  dsimp only at hcost
  have hinput : Fin.cons k' args =
      (![k',r' 0,r' 1,r' 2,r' 3,r' 4,r' 5,r' 6,r' 7,r' 8,spare,F repeatOutput ![n',(0 : M)]] : Fin 12 → M) := by
    funext i
    fin_cases i <;> simp [args,PA194ActualLoopOrbit.frameArgs,PA194ActualSourceLoop.args]
  rw [hinput] at hcode
  change F PA194Transfer45PhysicalZeroCost.cost (fun _ => y) = _ at hcost
  rw [hcode] at hcost
  rw [←hcost] at hzero
  rw [PA194StepperCompose.modelStepperCompose,ho,hzero]
#print axioms completeExit
end models
end PA194Transfer45PhysicalExit
