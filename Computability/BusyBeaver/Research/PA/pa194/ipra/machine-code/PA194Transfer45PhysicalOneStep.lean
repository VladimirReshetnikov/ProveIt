import PA194Transfer45PhysicalCost
import PA194Site45TransferCodedStep
import PA194ModelTransferState
import PA194ActualTransfer45Source
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000
namespace PA194Transfer45PhysicalOneStep
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194ModelLoopState PA194ModelLoopFrame PA194ModelLoopCost PA194ControllerLoopFrame PA194OneSpareReturn PA194StateOne PA194UnaryRuns PA194BinaryDouble PA194FiniteControls PA194RegisterFile PA194RegisterPermutation PA194Path27Header BinaryTapeCodes PackedDecoderModel TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem exactOneStep (r : Fin 9 → M) (tail k n spare m : M) (hm : r 6 = m+1) :
    let x := packed ((k+1)+1) n spare (PA194ModelTransfer45Source.source r tail)
    F PA194Stepper.stepper ![F PA194Transfer45PhysicalCost.cost (fun _ => x),
      F (PA194ModelLoopFrameAt.frameAt 45 readers) (fun _ => x)] =
      F (PA194ModelLoopFrameAt.frameAt 45 readers)
        (fun _ => F (PA194ModelTransferState.next PA194ActualTransfer45Source.triple) (fun _ => x)) := by
  let r' := Function.update (Function.update r 3 (r 3+1)) 6 m
  let a := PA194ActualLoopOrbit.frameArgs r n spare
  let a' := PA194ActualLoopOrbit.frameArgs r' (n+1) spare
  have harg : a 6 = m+1 := by simpa [a,PA194ActualLoopOrbit.frameArgs,PA194ActualSourceLoop.args] using hm
  have he : physicalArgs a 10 = F repeatOutput ![n,(0 : M)] := by
    simp [a,physicalArgs,inputOrder,PA194ActualLoopOrbit.frameArgs,PA194ActualSourceLoop.args]
  have hp := (PA194Site45TransferCodedStep.codedStep k n tail m a harg he).2
  have hout : PA194Site46OutputFile.updated (Function.update a 6 m) n = a' := by
    funext i
    fin_cases i <;> simp [a,a',r',PA194Site46OutputFile.updated,PA194ActualLoopOrbit.frameArgs,
      PA194ActualSourceLoop.args,←modelAddOne] <;> rfl
  rw [hout] at hp
  have hc := PA194Transfer45PhysicalCost.modelCost r tail k n spare m hm
  dsimp only at hc
  have hinput : PA194Site45TransferCodedStep.input k n m a =
      (![k,n,m,r 0,r 1,r 2,r 3,r 4,r 5,r 6,r 7,r 8,spare,F repeatOutput ![n,(0 : M)]] : Fin 14 → M) := by
    funext i
    fin_cases i <;> simp [PA194Site45TransferCodedStep.input,a,PA194ActualLoopOrbit.frameArgs,PA194ActualSourceLoop.args]
  rw [hinput] at hp
  have hf := PA194Transfer45PhysicalFrame.frameSource r tail ((k+1)+1) n spare
  have hn := PA194ModelTransferState.modelNext PA194ActualTransfer45Source.triple ((k+1)+1) n spare (PA194ModelTransfer45Source.source r tail)
  have hs := PA194ActualTransfer45Source.oneLoop r tail m hm
  rw [hs] at hn
  change F (PA194ModelTransferState.next PA194ActualTransfer45Source.triple)
    (fun _ => packed ((k+1)+1) n spare (PA194ModelTransfer45Source.source r tail)) =
    packed (((k+1)+1)+1) (n+1) spare (PA194ModelTransfer45Source.source r' tail) at hn
  have hf' := PA194Transfer45PhysicalFrame.frameSource r' tail (((k+1)+1)+1) (n+1) spare
  dsimp only at hn hf hf' ⊢
  rw [hc,hf,hn,hf']
  exact hp
#print axioms exactOneStep
end models
end PA194Transfer45PhysicalOneStep
