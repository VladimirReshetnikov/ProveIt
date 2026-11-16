import PA194Transfer45PhysicalOrbit
import PA194ModelLoopIteration

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace PA194Transfer45PhysicalOrbitCode
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

theorem completeLoop (r : Fin 9 → M) (tail k n spare : M) :
    let g := ((k+1)+1)
    let x := packed g n spare (PA194ModelTransfer45Source.source r tail)
    let y := packed (g+r 6) (n+r 6) spare (PA194ModelTransfer45Source.source (PA194ModelTransfer45Source.running r (r 6)) tail)
    F PA194Stepper.stepper ![F (timeCode (PA194ModelTransferState.next PA194ActualTransfer45Source.triple)
      PA194Transfer45PhysicalCost.cost) ![r 6,x],F (PA194ModelLoopFrameAt.frameAt 45 readers) (fun _ => x)] =
      F (PA194ModelLoopFrameAt.frameAt 45 readers) (fun _ => y) := by
  let g := ((k+1)+1)
  let r' := PA194ModelTransfer45Source.running r (r 6)
  have hf := PA194Transfer45PhysicalFrame.frameSource r tail g n spare
  have hf' := PA194Transfer45PhysicalFrame.frameSource r' tail (g+r 6) (n+r 6) spare
  have hp := PA194Transfer45PhysicalOrbit.physicalOrbit r tail k n spare (r 6) (le_refl _)
  dsimp only at hp ⊢
  rw [←hf,←hf'] at hp
  exact hp
#print axioms completeLoop
end models
end PA194Transfer45PhysicalOrbitCode
