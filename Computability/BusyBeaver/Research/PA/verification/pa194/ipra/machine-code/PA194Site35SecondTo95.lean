import PA194Site35SecondTo71
import PA194GenericRightScan
import PA194OnesCommute
import PA194Site34PositivePath
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site35SecondTo95
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation PA194RegisterFile BinaryTapeCodes TableDispatch PA194Path27Header PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PA194BinaryDouble PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem scanTo95 (k : M) (args : Fin 11 → M) :
    let n := (k+1)+1
    let f := F sourceFileCode args
    let e := physicalArgs args
    let p := F ones ![e 0+1,F (fileCode 9) (fun i => e i.succ)]
    let c := F addCode ![F addCode ![modelNumeral M 10,n+1],(1 : M)]
    let first := F addCode ![F addCode ![c,(k+1)+1],modelNumeral M 24]
    let left := F ones ![n,modelNumeral M 804]
    F PA194Stepper.stepper ![F addCode ![F addCode ![F addCode ![first,modelNumeral M 9],n],modelNumeral M 1],
      PA194SourceSite31Physical.physicalFrame 35 n args] =
      F pairCode ![modelNumeral M 95,F pairCode ![left+left,p]] := by
  dsimp only
  let n := (k+1)+1
  let f := F sourceFileCode args
  let e := physicalArgs args
  let p := F ones ![e 0+1,F (fileCode 9) (fun i => e i.succ)]
  let d := (1 : M)+(f+f)
  let v := (1 : M)+(d+d)
  have hf : f = p+p := by rw [show f = F (fileCode 10) e from PA194RegisterPermutation.modelSourceFile args,PA194RegisterFile.modelFileSucc,PA194RegisterFile.modelBlock]
  have hcomm (t a : M) : F ones ![t,(1 : M)+(a+a)] = F ones ![t+1,a] := by
    have hadd : (1 : M)+(a+a) = a+a+1 := by ac_rfl
    rw [hadd,PA194OnesCommute.modelOnesCommute]
    change _ = F ones ![F addCode ![t,F oneCode Fin.elim0],a]
    rw [modelAddOne,modelOnesSucc]
  have hv : F ones ![k,v] = F ones ![n,f] := by
    dsimp only [v,d,n]
    rw [hcomm,hcomm]
  have h := PA194Site35SecondTo71.to71 k args
  dsimp only at h
  change _ = F pairCode ![modelNumeral M 71,F pairCode ![modelNumeral M 804,F ones ![k,v]]] at h
  rw [hv,hf] at h
  have loop71 (a b : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 71,F pairCode ![a,b+b+1]]) =
      F pairCode ![modelNumeral M 71,F pairCode ![a+a+1,b]] := by
    have hh := PA194RightRows.rightOne 71 1 71 (by decide) (by decide +kernel) a b
    simpa only [modelNumeralOne] using hh
  have hs := PA194GenericRightScan.modelFullScan 71 loop71 n (modelNumeral M 804) (p+p)
  have he := PA194RightRows.rightZero 71 0 95 (by decide) (by decide +kernel) (F ones ![n,modelNumeral M 804]) p
  simp only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] at he
  have he1 : F PA194Stepper.stepper ![modelNumeral M 1,F pairCode ![modelNumeral M 71,
      F pairCode ![F ones ![n,modelNumeral M 804],p+p]]] =
      F pairCode ![modelNumeral M 95,F pairCode ![F ones ![n,modelNumeral M 804]+F ones ![n,modelNumeral M 804],p]] := by
    change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 0),_] = _
    rw [PA194Stepper.modelStepperSucc,show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,PA194Stepper.modelStepperZero,he]
  rw [PA194StepperCompose.modelStepperCompose,PA194StepperCompose.modelStepperCompose,h,hs,he1]
#print axioms scanTo95
end models
end PA194Site35SecondTo95
