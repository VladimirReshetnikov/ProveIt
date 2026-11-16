import PA194RestorePhysicalExit
import PA194SourceSite34PositivePhysical
import PA194SourceSite35Physical
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site35RestoreEntry
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194ModelLoopIteration PA194RegisterPermutation PA194OneSpareReturn PA194SourceSite31Physical PA194ModelTransferState PA194RestorePhysicalOrbit TableDispatch PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem restoreFeedsSite35 (r : Fin 9 → M) (tail k n spare m : M) :
    let r' := PA194ModelRestoreSource.running r (r 6)
    let k' := k+r 6
    let n' := n+r 6
    let args := PA194ActualLoopOrbit.frameArgs r' n' spare
    let output := PA194Site31OutputFile.updated args n'
    let next := Function.update output 8 m
    output 8 = m+1 →
    let g := ((k+1)+1)+1
    let e : Fin 13 → M := ![r' 0,r' 1,r' 2,r' 3,r' 4,r' 5,r' 6,r' 7,r' 8,tail,k'+1,n',spare]
    let x := PA194ModelLoopState.packed g n spare (PA194ModelRestoreSource.source r tail)
    let orbitClock := F (timeCode (PA194ModelTransferState.next PA194ActualRestoreSource.triple)
      PA194RestorePhysicalCost.cost) ![r 6,x]
    let restoreClock := F addCode ![F addCode ![orbitClock,F PA194Site31CodedClock.clockCode e],
      F PA194Site32ZeroClockCode.clockCode (Fin.cons k' output)]
    F PA194Stepper.stepper ![F addCode ![PA194Site34PositiveTo16.clock (k'+1) output,modelNumeral M 23],
      F PA194Stepper.stepper ![restoreClock,physicalFrame 31 g (PA194ActualLoopOrbit.frameArgs r n spare)]] =
      physicalFrame 35 (((k'+1)+1)+1) next ∧
    physicalArgs next 10 = F repeatOutput ![F Code.succ (fun _ => n'),(0 : M)] := by
  dsimp only
  intro hm
  let r' := PA194ModelRestoreSource.running r (r 6)
  let k' := k+r 6
  let n' := n+r 6
  let args := PA194ActualLoopOrbit.frameArgs r' n' spare
  let output := PA194Site31OutputFile.updated args n'
  let next := Function.update output 8 m
  have hrestore := PA194RestorePhysicalExit.completeExit r tail k n spare
  dsimp only at hrestore
  have h34 := (PA194SourceSite34PositivePhysical.positiveBranch (k'+1) tail m output hm).2
  refine ⟨?_,?_⟩
  · rw [hrestore,h34]
  · change Function.update output 8 m 10 = _
    simp [next,output,n',PA194Site31OutputFile.updated]
#print axioms restoreFeedsSite35
end models
end PA194Site35RestoreEntry
