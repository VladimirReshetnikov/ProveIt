import PA194FirstThreePositiveScan
import PA194ScanInvariant
import PA194CarryEntry
import PA194FirstThreeFirstTo42
import PA194State42Boundary
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194CarryThreeFile
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194ScanInvariant PA194CarryEntry PA194StateOne PA194FirstThreeFirstTo42 PA194State42Boundary PA194FirstThreeFirstTo42 PA194State42Boundary PA194FirstThreeBoundary PA194PositiveMarkerRoute PA194FirstFiveFirstCore PA194FirstFiveTo84 PA194EightyFourScan PA194State42Boundary PA194PositiveMarkCycle
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

theorem cycleThree (v l p : M) :
    let a := F ones ![v,l+l]
    F PA194Stepper.stepper ![(1 : M)+(v+1),
      F pairCode ![modelNumeral M 3,F pairCode ![l,F ones ![v+1,p+p]]]] =
    F pairCode ![modelNumeral M 3,F pairCode ![a+a+1,p]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  have ho : F ones ![v+1,p+p] = F ones ![v,p+p]+F ones ![v,p+p]+1 := by
    change F ones ![F addCode ![v,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelOnesSucc]
  rw [ho]
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  let c := F pairCode ![modelNumeral M 3,F pairCode ![l,F ones ![v,p+p]+F ones ![v,p+p]+1]]
  have h0 : F PA194Stepper.stepper ![(0 : M),c] = c := PA194Stepper.modelStepperZero c
  have hs (x : M) : F PA194Stepper.stepper ![x+1,c] = F PackedClock.encodedStep (fun _ => F PA194Stepper.stepper ![x,c]) := by
    change F PA194Stepper.stepper ![F addCode ![x,F oneCode Fin.elim0],c] = _
    rw [modelAddOne,PA194Stepper.modelStepperSucc]
  have h : F PA194Stepper.stepper ![(1 : M),c] = F pairCode ![modelNumeral M 1,F pairCode ![l+l,F ones ![v,p+p]]] := by
    have h' := hs (0 : M)
    rw [h0] at h'
    dsimp only [c] at h'
    rw [modelPackedCarryThree] at h'
    simpa only [zero_add] using h' 
  rw [h]
  exact PA194FirstThreePositiveScan.scanTo3 v (l+l) p

theorem carryThreeAcross (n : Nat) (e : Fin (n+1) → M) (v l p : M)
    (hend : e (Fin.last n) = p+p) :
    ∃ time out : M, F PA194Stepper.stepper ![time,
      F pairCode ![modelNumeral M 3,F pairCode ![l,F ones ![v+1,F (fileCode n) e]]]] =
      F pairCode ![modelNumeral M 3,F pairCode ![out,p]] := by
  induction n generalizing v l with
  | zero =>
    have he : F (fileCode 0) e = p+p := by
      change F (.proj 0) e = _
      rw [modelProjection]
      exact hend
    refine ⟨(1 : M)+(v+1), F ones ![v,l+l]+F ones ![v,l+l]+1, ?_⟩
    rw [he]
    exact cycleThree v l p
  | succ n ih =>
    let ee : Fin (n+1) → M := fun i => e i.succ
    let z := F (fileCode n) ee
    let q := F ones ![e 0+1,z]
    have hf : F (fileCode (n+1)) e = q+q := by
      rw [modelFileSucc,modelBlock]
    have he : ee (Fin.last n) = p+p := hend
    have hn := ih ee (e 0) (F ones ![v,l+l]+F ones ![v,l+l]+1) he
    obtain ⟨t,out,hr⟩ := hn
    refine ⟨((1 : M)+(v+1))+t,out,?_⟩
    rw [hf]
    change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
    rw [PA194StepperCompose.modelStepperCompose,cycleThree]
    exact hr
#print axioms carryThreeAcross
end models
end PA194CarryThreeFile
