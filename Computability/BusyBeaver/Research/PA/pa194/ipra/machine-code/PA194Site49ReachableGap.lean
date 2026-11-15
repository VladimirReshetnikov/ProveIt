import PA194Transfer42PhysicalExit
import PA194Transfer45PhysicalExit
import PA194SourceSite48PositivePhysical
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA194Site49ReachableGap
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194ModelLoopIteration PA194RegisterPermutation PA194SourceSite31Physical PA194ModelTransferState TableDispatch PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
noncomputable def stage48 (k : M) (args : Fin 11 → M) (x : M) : M :=
  let vec := PA194Site48MarkedFile.prefixArgs args
  let cost := ((k+1)+F (PA194CarryFile.costCode 4) vec)+modelNumeral M 2
  F PA194Stepper.stepper ![cost,
    F PA194Stepper.stepper ![modelNumeral M 9,
      F PA194Stepper.stepper ![modelNumeral M 22,
        F PA194Stepper.stepper ![((k+1)+1)+1,
          F PA194Stepper.stepper ![PA194Site48SecondTo17.fourCost args,
            F PA194Stepper.stepper ![modelNumeral M 3,
              F PA194Stepper.stepper ![PA194Site48SecondTo17.clock14 k args,x]]]]]]]

theorem reaches49 (r : Fin 9 → M) (tail k n spare m : M) :
    let r42 := PA194ModelTransfer42Source.running r (r 7)
    let n42 := n+r 7
    let k45 := (k+r 7)+1
    let r45 := PA194ModelTransfer45Source.running r42 (r42 6)
    let n45 := n42+r42 6
    let k48 := (k45+r42 6)+1
    let args := PA194ActualLoopOrbit.frameArgs r45 n45 spare
    args 3 = m+1 →
    let x42 := PA194ModelLoopState.packed ((k+1)+1) n spare (PA194ModelTransfer42Source.source r tail)
    let y42 := PA194ModelLoopState.packed (((k+r 7)+1)+1) n42 spare (PA194ModelTransfer42Source.source r42 tail)
    let c42 := F addCode ![F (PA194ModelLoopIteration.timeCode (PA194ModelTransferState.next PA194ActualTransfer42Source.triple) PA194Transfer42PhysicalCost.cost) ![r 7,x42],F PA194Transfer42PhysicalZeroCost.cost (fun _ => y42)]
    let x45 := PA194ModelLoopState.packed ((k45+1)+1) n42 spare (PA194ModelTransfer45Source.source r42 tail)
    let y45 := PA194ModelLoopState.packed (((k45+r42 6)+1)+1) n45 spare (PA194ModelTransfer45Source.source r45 tail)
    let c45 := F addCode ![F (PA194ModelLoopIteration.timeCode (PA194ModelTransferState.next PA194ActualTransfer45Source.triple) PA194Transfer45PhysicalCost.cost) ![r42 6,x45],F PA194Transfer45PhysicalZeroCost.cost (fun _ => y45)]
    let c48 := F addCode ![PA194Site48PositiveTo16.clock k48 args,modelNumeral M 21]
    F PA194Stepper.stepper ![c48,stage48 k48 args
      (F PA194Stepper.stepper ![c45,F PA194Stepper.stepper ![c42,
        physicalFrame 42 ((k+1)+1) (PA194ActualLoopOrbit.frameArgs r n spare)]])] =
      physicalFrame 49 k48 (Function.update args 3 m) ∧
    ∃ q : M, k48 = (q+1)+1 := by
  dsimp only
  intro hm
  let r42 := PA194ModelTransfer42Source.running r (r 7)
  let n42 := n+r 7
  let k45 := (k+r 7)+1
  let r45 := PA194ModelTransfer45Source.running r42 (r42 6)
  let n45 := n42+r42 6
  let k48 := (k45+r42 6)+1
  let args := PA194ActualLoopOrbit.frameArgs r45 n45 spare
  have h42 := PA194Transfer42PhysicalExit.completeExit r tail k n spare
  have h45 := PA194Transfer45PhysicalExit.completeExit r42 tail k45 n42 spare
  dsimp only at h42 h45
  have h48 := (PA194SourceSite48PositivePhysical.positiveBranch k48 tail m args hm).2
  refine ⟨?_,?_⟩
  · change F PA194Stepper.stepper ![_,stage48 k48 args (F PA194Stepper.stepper ![_,F PA194Stepper.stepper ![_,_]])] = _
    rw [h42,h45]
    change F PA194Stepper.stepper ![_,PA194Site48Branch.runTo4 k48 args] = _
    exact h48
  · refine ⟨(k+r 7)+r42 6,?_⟩
    simp only [r42,k48,k45,add_assoc,add_comm,add_left_comm]
#print axioms reaches49
end models
end PA194Site49ReachableGap
