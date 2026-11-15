import PA194RestorePhysicalCost
import PA194SourceSite31FullyCoded
import PA194ModelTransferState
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000
namespace PA194RestorePhysicalOneStep
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
    let x := packed (((k+1)+1)+1) n spare (PA194ModelRestoreSource.source r tail)
    F PA194Stepper.stepper ![F PA194RestorePhysicalCost.cost (fun _ => x),
      F (PA194ModelLoopFrameAt.frameAt 31 readers) (fun _ => x)] =
      F (PA194ModelLoopFrameAt.frameAt 31 readers)
        (fun _ => F (PA194ModelTransferState.next PA194ActualRestoreSource.triple) (fun _ => x)) := by
  let e : Fin 14 → M := ![r 0,r 1,r 2,r 3,r 4,r 5,r 6,r 7,r 8,(0 : M),k+1,n,spare,k]
  let r' := Function.update (Function.update r 0 (r 0+1)) 6 m
  let a := PA194ActualLoopOrbit.frameArgs r n spare
  let a' := PA194ActualLoopOrbit.frameArgs r' (n+1) spare
  have hg : PA194Site31TransferClockCode.env13 e 10 = e 13+1 := by rfl
  have he : PA194Site31TransferClockCode.env13 e 6 = m+1 := by simpa [e,PA194Site31TransferClockCode.env13] using hm
  have hp := (PA194SourceSite31FullyCoded.oneLoop e m hg he).2
  have ha : PA194Site31SentenceClock.args (PA194Site31TransferClockCode.env13 e) = a := by
    funext i
    fin_cases i <;> simp [a,e,PA194Site31TransferClockCode.env13,PA194Site31SentenceClock.args,
      PA194Site31SentenceClock.regs,PA194ActualLoopOrbit.frameArgs,PA194ActualSourceLoop.args]
  have hout : Function.update (PA194Site31OutputFile.updated a n) 6 m = a' := by
    funext i
    fin_cases i <;> simp [a,a',r',PA194Site31OutputFile.updated,PA194ActualLoopOrbit.frameArgs,
      PA194ActualSourceLoop.args,←modelAddOne] <;> rfl
  change F PA194Stepper.stepper ![F PA194Site31TransferClockCode.clockCode e,
      PA194SourceSite31Physical.physicalFrame 31 (((k+1)+1)+1)
        (PA194Site31SentenceClock.args (PA194Site31TransferClockCode.env13 e))] =
    PA194SourceSite31Physical.physicalFrame 31 ((((k+1)+1)+1)+1)
      (Function.update (PA194Site31OutputFile.updated
        (PA194Site31SentenceClock.args (PA194Site31TransferClockCode.env13 e)) n) 6 m) at hp
  rw [ha,hout] at hp
  have hc := PA194RestorePhysicalCost.modelCost r tail k n spare
  dsimp only at hc
  change F PA194RestorePhysicalCost.cost (fun _ => packed (((k+1)+1)+1) n spare (PA194ModelRestoreSource.source r tail)) =
    F PA194Site31TransferClockCode.clockCode e at hc
  have hf := PA194RestorePhysicalFrame.frameSource r tail (((k+1)+1)+1) n spare
  have hn := PA194ModelTransferState.modelNext PA194ActualRestoreSource.triple (((k+1)+1)+1) n spare (PA194ModelRestoreSource.source r tail)
  have hs := PA194ActualRestoreSource.oneLoop r tail m hm
  rw [hs] at hn
  change F (PA194ModelTransferState.next PA194ActualRestoreSource.triple)
    (fun _ => packed (((k+1)+1)+1) n spare (PA194ModelRestoreSource.source r tail)) =
    packed ((((k+1)+1)+1)+1) (n+1) spare (PA194ModelRestoreSource.source r' tail) at hn
  have hf' := PA194RestorePhysicalFrame.frameSource r' tail ((((k+1)+1)+1)+1) (n+1) spare
  dsimp only at hn hf hf' ⊢
  rw [hc,hf,hn,hf']
  exact hp
#print axioms exactOneStep
end models
end PA194RestorePhysicalOneStep
