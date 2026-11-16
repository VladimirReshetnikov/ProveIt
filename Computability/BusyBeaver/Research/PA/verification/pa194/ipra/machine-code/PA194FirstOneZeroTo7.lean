import PA194FirstOneZeroTo3
import PA194CarryThreeExactFile
import PA194ThreeBlankTail
import PA194FirstTwoPositiveTo71
import PA194FirstThreePositiveScan
import PA194RightRows
import PA194PositiveMarkerRoute
import PA194FirstFiveFirstCore
import PA194FirstFiveTo84
import PA194EightyFourScan
import PA194State42Boundary
import PA194PositiveMarkCycle
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194FirstOneZeroTo7
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194FirstOneZeroTo3 PA194FirstOneZeroTo1 PA194FirstTwoPositiveTo71 PA194FirstThreePositiveScan PA194FirstTwoFirstTo73 PA194FirstTwoFirstTo86 PA194RightRows PA194FirstTwoBoundary PA194PositiveMarkerRoute PA194FirstFiveFirstCore PA194FirstFiveTo84 PA194EightyFourScan PA194State42Boundary PA194PositiveMarkCycle
open BinaryTapeCodes PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble
open PA194PositiveThreshold PA194HeaderController PA194PositiveMarkerRoute PA194ThresholdCycle
open PA194MarkAll PA194CarryFile PA194RegisterFile PA194ReturnFile PA194MarkerScan
open PRAModelIOpenPairing TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem markerFirstOneZeroBlankTo7 (e : Fin 2 → M) (rest : Fin 9 → M) (u : M)
    (ht : e (Fin.last 1) =
      let t := F ones ![(0 : M),F (fileCode 8) rest]; (t+t+1)+(t+t+1))
    (hfirst : e 0 = modelNumeral M 1)
    (hblank : rest (Fin.last 8) = (0 : M)) :
    let z := u+u
    let z1 := z+z
    let z2 := z1+z1
    let z3 := z2+z2
    let z4 := z3+z3
    let l64 := z4+z4
    let x := ((l64+l64)+(l64+l64))+((l64+l64)+(l64+l64))+1
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    let xx := h+h+1
    let ll := (xx+xx)+(xx+xx)+1
    let a0 := ll+ll+1
    let d := (a0+a0)+(a0+a0)
    let l := (d+d)+(d+d)
    let left := F ones ![rest 0,l]
    let out := PA194CarryThreeExactFile.carried 6 (fun i => rest i.succ.succ)
      (rest ⟨1,by decide⟩) (left+left+1)
    let c3 := ((1 : M)+1)+1
    let c6 := c3+c3
    let c13 := (c6+c6)+1
    ∃ time : M, F PA194Stepper.stepper ![time,F pairCode ![modelNumeral M (markerControl ⟨1,by decide⟩),
      F pairCode ![x+x+1,F (fileCode 1) e]]] =
      F pairCode ![modelNumeral M 7,F pairCode ![out,c13]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let h := g+g+1
  let xx := h+h+1
  let ll := (xx+xx)+(xx+xx)+1
  let a0 := ll+ll+1
  let d := (a0+a0)+(a0+a0)
  let l := (d+d)+(d+d)
  let y := F ones ![rest 0,l]
  let ee : Fin 7 → M := fun i => rest i.succ.succ
  let q := F ones ![rest ⟨1,by decide⟩+1,F (fileCode 6) ee]
  let out := PA194CarryThreeExactFile.carried 6 ee (rest ⟨1,by decide⟩) (y+y+1)
  obtain ⟨time,p,hp,hm⟩ := markerFirstOneZeroBlankTo3 e rest u ht hfirst hblank
  have hf : F (fileCode 7) (fun i => rest i.succ) = q+q := by
    rw [modelFileSucc,modelBlock]
    rfl
  have hh := congrArg (fun z : M => F halfCode (fun _ => z)) (hf.symm.trans hp)
  rw [(modelDouble q).2,(modelDouble p).2] at hh
  have hq : p=q := hh.symm
  rw [hq] at hm
  have he : ee (Fin.last 6) = (0 : M)+(0 : M) := by
    simpa only [ee,Fin.succ_last,zero_add] using hblank
  obtain ⟨more,hcarry⟩ := PA194CarryThreeExactFile.carryThreeAcrossExact 6 ee (rest ⟨1,by decide⟩) (y+y+1) (0 : M) he
  refine ⟨(time+more)+modelNumeral M 5,?_⟩
  change F PA194Stepper.stepper ![F addCode ![time+more,modelNumeral M 5],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![modelNumeral M 5,F PA194Stepper.stepper ![F addCode ![time,more],_]] = _
  rw [PA194StepperCompose.modelStepperCompose,hm,hcarry]
  exact PA194ThreeBlankTail.modelThreeBlankTail out
#print axioms markerFirstOneZeroBlankTo7
end models
end PA194FirstOneZeroTo7
