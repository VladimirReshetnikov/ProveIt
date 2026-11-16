import PA194FirstTwoPositiveTo71
import PA194GenericRightScan
import PA194State106Scan
import PA194GenericRightScan
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
namespace PA194FirstTwoPositiveTo95
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194FirstTwoPositiveTo71 PA194FirstTwoPositiveTo106 PA194FirstTwoPositiveTo85 PA194FirstTwoFirstTo73 PA194FirstTwoFirstTo86 PA194RightRows PA194FirstTwoBoundary PA194PositiveMarkerRoute PA194FirstFiveFirstCore PA194FirstFiveTo84 PA194EightyFourScan PA194State42Boundary PA194PositiveMarkCycle
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

theorem state71FileTo95 (n : Nat) (rest : Fin (n+2) → M) (l p : M)
    (hblank : rest (Fin.last (n+1)) = (0 : M))
    (hp : F (fileCode n) (fun i => rest i.succ) = p+p) :
    ∃ time left right : M, F PA194Stepper.stepper ![time,
      F pairCode ![modelNumeral M 71,F pairCode ![l,p]]] =
    F pairCode ![modelNumeral M 95,F pairCode ![left,right]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  cases n with
  | zero =>
    have hi : (0 : Fin 1).succ = Fin.last 1 := by decide
    rw [fileCode,modelProjection,hi,hblank] at hp
    have hz : (0 : M) = (0 : M)+(0 : M) := by simp only [zero_add]
    rw [hz] at hp
    have hh := congrArg (fun x : M => F halfCode (fun _ => x)) hp
    rw [(modelDouble (0 : M)).2,(modelDouble p).2] at hh
    subst p
    refine ⟨modelNumeral M 1,l+l,(0 : M),?_⟩
    change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 0),_] = _
    rw [PA194Stepper.modelStepperSucc,show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,PA194Stepper.modelStepperZero]
    have h := rightZero 71 0 95 (by decide) (by decide +kernel) l (0 : M)
    simpa only [show modelNumeral M 0 = (0 : M) from rfl,zero_add,add_zero] using h
  | succ n =>
    let next : Fin (n+2) → M := fun i => rest i.succ
    have hblank' : next (Fin.last (n+1)) = (0 : M) := by simpa only [next,Fin.succ_last] using hblank
    obtain ⟨q,hq⟩ := evenRemainingFile n next hblank'
    let a := F ones ![next 0+1,q+q]
    have hf : F (fileCode (n+1)) (fun i => rest i.succ) = a+a := by
      rw [modelFileSucc,modelBlock]
      change F ones ![next 0+1,F (fileCode n) (fun i => next i.succ)] + _ = _
      rw [hq]
    rw [hf] at hp
    have hh := congrArg (fun x : M => F halfCode (fun _ => x)) hp
    rw [(modelDouble a).2,(modelDouble p).2] at hh
    subst p
    have hloop (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 71,F pairCode ![x,y+y+1]]) =
        F pairCode ![modelNumeral M 71,F pairCode ![x+x+1,y]] := by
      have h := rightOne 71 1 71 (by decide) (by decide +kernel) x y
      simpa only [PA194StateOne.modelNumeralOne] using h
    have hs := PA194GenericRightScan.modelFullScan 71 hloop (next 0+1) l (q+q)
    let x := F ones ![next 0+1,l]
    have hx := rightZero 71 0 95 (by decide) (by decide +kernel) x q
    simp only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] at hx
    refine ⟨(next 0+1)+1,x+x,q,?_⟩
    change F PA194Stepper.stepper ![F addCode ![next 0+1,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,PA194Stepper.modelStepperSucc,hs,hx]
theorem markerFirstTwoPositiveBlankTo95 (n : Nat) (e : Fin 2 → M) (rest : Fin (n+2) → M)
    (u k : M)
    (ht : e (Fin.last 1) =
      let t := F ones ![k+1,F (fileCode (n+1)) rest]; (t+t+1)+(t+t+1))
    (hfirst : e 0 = modelNumeral M 2)
    (hblank : rest (Fin.last (n+1)) = (0 : M)) :
    let z := u+u
    let z1 := z+z
    let z2 := z1+z1
    let z3 := z2+z2
    let z4 := z3+z3
    let l64 := z4+z4
    let x := ((l64+l64)+(l64+l64))+((l64+l64)+(l64+l64))+1
    ∃ time left right : M, F PA194Stepper.stepper ![time,
      F pairCode ![modelNumeral M (markerControl ⟨1,by decide⟩),F pairCode ![x+x+1,F (fileCode 1) e]]] =
    F pairCode ![modelNumeral M 95,F pairCode ![left,right]] := by
  dsimp only
  obtain ⟨t,l,p,hfile,hm⟩ := markerFirstTwoPositiveBlankTo71WithFile n e rest u k ht hfirst hblank
  obtain ⟨more,left,right,hnext⟩ := state71FileTo95 n rest l p hblank hfile
  refine ⟨t+more,left,right,?_⟩
  change F PA194Stepper.stepper ![F addCode ![t,more],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hm]
  exact hnext
#print axioms markerFirstTwoPositiveBlankTo95
#print axioms state71FileTo95
end models
end PA194FirstTwoPositiveTo95
