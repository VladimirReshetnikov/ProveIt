import PA194Site27ZeroCostInput
import PA194ModelLoopFrameAt
import PA194Site27ZeroClockPhysical
import PA194Site27ZeroFile
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace PA194Site27ZeroCodedStep
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion PA194ModelLoopState PA194ModelLoopFrame PA194ModelLoopFrameAt PA194ModelLoopCost PA194ModelLoopCostInputs PA194Site27ZeroCostInput PA194OneSpareReturn PA194StateOne PA194ZeroRuns PA194UnaryRuns PA194BinaryDouble PA194FiniteControls BinaryTapeCodes PackedDecoderModel TableDispatch PA194RegisterFile PA194RegisterPermutation PA194Path27Header
open PA194ActualLoopOrbit PA194ControllerLoopFrame PA194ModelSourceLoop PA194SourceSite25Physical
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem zeroStep (c : Code 12) (r : Fin 9 → M) (tail k n spare : M) (hz : r 0 = (0 : M))
    (hc : F c (Fin.cases k (frameArgs r n spare)) = PA194Site27ZeroClockPhysical.clock24 k (frameArgs r n spare)) :
    let x := packed ((k+1)+1) n spare (PA194ModelSourceLoop.source r tail)
    F PA194Stepper.stepper ![F (zeroCost c) (fun _ => x), F (frameAt 27 readers) (fun _ => x)] =
      F (frameAt 31 readers) (fun _ => x) := by
  dsimp only
  let a := frameArgs r n spare
  have ha0 : a 0 = (0 : M) := by simpa [a,frameArgs,PA194ActualSourceLoop.args] using hz
  have ht : a 10 = F repeatOutput ![n,(0 : M)] := by simp [a,frameArgs]
  have hs : a 9 = spare := by simp [a,frameArgs]
  have hsrc := controllerSource r n spare tail
  have hf27 := frameSourceAt 27 a ((k+1)+1) n tail ht
  have hf31 := frameSourceAt 31 a ((k+1)+1) n tail ht
  rw [hs,hsrc] at hf27 hf31
  change F (frameAt 27 readers) (fun _ => packed ((k+1)+1) n spare (PA194ModelSourceLoop.source r tail)) = physicalFrame 27 ((k+1)+1) a at hf27
  change F (frameAt 31 readers) (fun _ => packed ((k+1)+1) n spare (PA194ModelSourceLoop.source r tail)) = physicalFrame 31 ((k+1)+1) a at hf31
  have hfile := PA194Site27ZeroFile.returnedIsSourceFile a ha0
  have h := PA194Site27ZeroClockPhysical.zeroBranchWithFile k a ha0 hfile
  have hcost := PA194Site27ZeroCostInput.cost c r tail k n spare
  change F c (Fin.cases k a) = PA194Site27ZeroClockPhysical.clock24 k a at hc
  rw [←hc,←hcost,←hf27,←hf31] at h
  exact h
#print axioms zeroStep
end models
end PA194Site27ZeroCodedStep
