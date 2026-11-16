import PA194Site31DynamicTail
import PA194IncrementFront
import PA194ReturnFileMeaning
import PA194OnesCommute
import PA194PrefixReturn
import PA194CompressedTape
import PA194OneSpareFileRoundTrip
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194RepeatedSpareIncrement
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194RegisterFile PA194MarkedFile PA194CarryFile PA194UnaryRuns PA194IncrementFront PA194ReturnFile PA194ReturnFileMeaning PA194ReturnCell PA194OnesCommute
open BinaryTapeCodes TableDispatch PA194OneSpareReturn
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

/-- Physical increment at the start of a marked file, with an arbitrary fixed number
of following ordinary registers and a model-valued number of trailing spares. -/
theorem increment (m : Nat) (n l : M) (e : Fin (m+2) → M)
    (he : e (Fin.last (m+1)) = F repeatOutput ![n,(0 : M)]) :
    let c := F (costCode m) (fun i => e i.succ)
    let front := (((1 : M)+1)+e 0)+c
    let six := ((1 : M)+1)+((1 : M)+1)+((1 : M)+1)
    let tail := F repeatOutput ![n,six]
    let rest := F (returnCode m) (Fin.cases tail (fun i => e i.succ))
    let result := F block ![e 0+1,rest]
    F PA194Stepper.stepper ![((e 0+1)+1+1),
      F PA194Stepper.stepper ![c,
        F PA194Stepper.stepper ![(n+n)+n,
          F PA194Stepper.stepper ![modelNumeral M 2,
            F PA194Stepper.stepper ![modelNumeral M 3,
              F PA194Stepper.stepper ![(n+n)+n,
                F PA194Stepper.stepper ![(1 : M),
                  F PA194Stepper.stepper ![front,F pairCode ![modelNumeral M 2,
                    F pairCode ![l,F (markedFile m) e]]]]]]]]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+(result+result)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let selected := F ones ![e 0,(l+l)+(l+l)+1]
  let six := ((1 : M)+1)+((1 : M)+1)+((1 : M)+1)
  let tail := F repeatOutput ![n,six]
  let rest := F (returnCode m) (Fin.cases tail (fun i => e i.succ))
  have hs := modelSelectedAndCarry m e l
  rw [he] at hs
  have ht := PA194Site31DynamicTail.tailRoundTrip n (F (leftCode m) (Fin.cases selected (fun i => e i.succ)))
  dsimp only at ht
  have hr := modelReturnFile m (fun i => e i.succ) selected tail
  have hc := modelReturnCell (e 0+1) l rest
  dsimp only at hc
  have hselected : selected = F ones ![e 0+1,l+l] := by
    dsimp [selected]
    have hs : F ones ![e 0+1,l+l] = F ones ![e 0,l+l]+F ones ![e 0,l+l]+1 := by
      change F ones ![F addCode ![e 0,F oneCode Fin.elim0],_] = _
      rw [modelAddOne,modelOnesSucc]
    rw [modelOnesCommute,hs]
  rw [hs,ht,hr,hselected,hc]
  have heq : (1 : M)+rest+rest = rest+rest+1 := by simp only [add_comm,add_left_comm]
  rw [heq,←modelReturnBlock]
  dsimp only [rest,tail,six]
  simp only [add_assoc]
/-- Increment with an arbitrary fixed prefix and model-valued trailing spare count. -/
theorem incrementAnywhere (p m : Nat) (count l : M)
    (ep : Fin (p+1) → M) (e : Fin (m+2) → M)
    (hp : ep (Fin.last p) = F (markedFile m) e)
    (he : e (Fin.last (m+1)) = F repeatOutput ![count,(0 : M)]) :
    let tail := F repeatOutput ![count+1,(0 : M)]
    let rest := F (returnCode m) (Fin.cases tail (fun i => e i.succ))
    let result := F block ![e 0+1,rest]
    let out := F (returnCode p) (Fin.cases result ep)
    PA194CompressedTape.Reach
      (PA194BidirectionalRunScan.frame true 2 l (F (fileCode p) ep))
      (PA194BidirectionalRunScan.frame false 7 out l) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let left := F (PA194PrefixFile.leftCode p) (Fin.cases l ep)
  let tail := F repeatOutput ![count+1,(0 : M)]
  let rest := F (returnCode m) (Fin.cases tail (fun i => e i.succ))
  let result := F block ![e 0+1,rest]
  have htail : F repeatOutput ![count,((1 : M)+1)+((1 : M)+1)+((1 : M)+1)] = tail := by
    dsimp only [tail]
    have hn : F Code.succ (fun _ => count) = count+1 := (modelAddOne count).symm
    rw [← PA194OneSpareFileRoundTrip.outputBlockZero, PA194OneSpareIdentities.modelOutputShift, hn]
  have h0 := PA194PrefixFile.modelPrefixFile p ep l
  rw [hp] at h0
  have h1 := increment m count left e he
  dsimp only at h1
  rw [htail] at h1
  simp only [← PA194StepperCompose.modelStepperCompose] at h1
  have h2 := PA194PrefixReturn.modelReturnPrefixFile p ep l result
  dsimp only at h2
  simp only [add_assoc] at h2
  exact PA194CompressedTape.trans ⟨_,h0⟩ (PA194CompressedTape.trans ⟨_,h1⟩ ⟨_,h2⟩)

#print axioms increment
#print axioms incrementAnywhere
end models
end PA194RepeatedSpareIncrement
