import PA194Transfer42PhysicalOneStep
import PA194ModelLoopIteration

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace PA194Transfer42PhysicalOrbit
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

theorem physicalOrbit (r : Fin 9 → M) (tail k n spare steps : M) (h : steps ≤ r 7) :
    let g := ((k+1)+1)
    let x := packed g n spare (PA194ModelTransfer42Source.source r tail)
    let a := frameArgs r n spare
    let a' := frameArgs (PA194ModelTransfer42Source.running r steps) (n+steps) spare
    F PA194Stepper.stepper ![F (timeCode (PA194ModelTransferState.next PA194ActualTransfer42Source.triple)
      PA194Transfer42PhysicalCost.cost) ![steps,x],PA194SourceSite31Physical.physicalFrame 42 g a] =
        PA194SourceSite31Physical.physicalFrame 42 (g+steps) a' := by
  let g := ((k+1)+1)
  let x := packed g n spare (PA194ModelTransfer42Source.source r tail)
  let frame := PA194ModelLoopFrameAt.frameAt 42 PA194ControllerLoopFrame.readers
  have hstep : ∀ i, i < r 7 →
        F PA194Stepper.stepper ![F PA194Transfer42PhysicalCost.cost
          (fun _ => F (iterCode (PA194ModelTransferState.next PA194ActualTransfer42Source.triple)) ![i,x]),
          F frame (fun _ => F (iterCode (PA194ModelTransferState.next PA194ActualTransfer42Source.triple)) ![i,x])] =
        F frame (fun _ => F (PA194ModelTransferState.next PA194ActualTransfer42Source.triple)
          (fun _ => F (iterCode (PA194ModelTransferState.next PA194ActualTransfer42Source.triple)) ![i,x])) := by
    intro i hi
    let m := F predCode (fun _ => F subCode ![r 7,i])
    have hp : (0 : M) < F subCode ![r 7,i] := by
      rw [modelSubAsTsub]
      exact tsub_pos_of_lt hi
    have hs := (PRAExhaustion.modelZeroOrSuccPred (F subCode ![r 7,i])).resolve_left (ne_of_gt hp)
    rw [←modelAddOne] at hs
    change m+1 = F subCode ![r 7,i] at hs
    have hm : PA194ModelTransfer42Source.running r i 7 = m+1 := by
      change F subCode ![r 7,i] = m+1
      exact hs.symm
    have hiter := PA194ModelTransferState.iterPacked (M := M) PA194ActualTransfer42Source.triple i g n spare (PA194ModelTransfer42Source.source r tail)
    rw [PA194ActualTransfer42Source.sourceIteration r tail i (le_of_lt hi)] at hiter
    have hg : g+i = (((k+i)+1)+1) := by dsimp [g]; simp [add_assoc,add_comm,add_left_comm]
    have hexact := PA194Transfer42PhysicalOneStep.exactOneStep (PA194ModelTransfer42Source.running r i) tail (k+i) (n+i) spare m hm
    dsimp only at hexact
    change F (iterCode (PA194ModelTransferState.next PA194ActualTransfer42Source.triple)) ![i,x] =
      packed (g+i) (n+i) spare (PA194ModelTransfer42Source.source (PA194ModelTransfer42Source.running r i) tail) at hiter
    rw [hiter,hg]
    exact hexact
  have hi := PA194ModelLoopIteration.modelIteration (M := M)
    (PA194ModelTransferState.next PA194ActualTransfer42Source.triple) PA194Transfer42PhysicalCost.cost frame (r 7) x steps hstep h
  have hiter := PA194ModelTransferState.iterPacked (M := M) PA194ActualTransfer42Source.triple steps g n spare (PA194ModelTransfer42Source.source r tail)
  rw [PA194ActualTransfer42Source.sourceIteration r tail steps h] at hiter
  change F (iterCode (PA194ModelTransferState.next PA194ActualTransfer42Source.triple)) ![steps,x] =
    packed (g+steps) (n+steps) spare (PA194ModelTransfer42Source.source (PA194ModelTransfer42Source.running r steps) tail) at hiter
  have hf := PA194Transfer42PhysicalFrame.frameSource r tail g n spare
  have hf' := PA194Transfer42PhysicalFrame.frameSource (PA194ModelTransfer42Source.running r steps) tail (g+steps) (n+steps) spare
  change F frame (fun _ => x) = _ at hf
  rw [hiter,hf'] at hi
  rw [hf] at hi
  exact hi
#print axioms physicalOrbit
end models
end PA194Transfer42PhysicalOrbit
