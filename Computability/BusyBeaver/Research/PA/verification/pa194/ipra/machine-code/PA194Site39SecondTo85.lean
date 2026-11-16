import PA194Site39SecondTo60
import PA194GenericRightScan
import PA194OnesCommute
import PA194RightRows
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site39SecondTo85
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation PA194RegisterFile BinaryTapeCodes TableDispatch PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PA194RightRows PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem to85 (k : M) (args : Fin 11 → M) :
    let n := (k+1)+1
    let e := physicalArgs args
    let p := F ones ![e 0+1,F (fileCode 9) (fun i => e i.succ)]
    let l := F ones ![n,modelNumeral M 12908]
    F PA194Stepper.stepper ![F addCode ![F addCode ![PA194Site39SecondTo60.firstClock k,modelNumeral M 15],n+1],
      PA194SourceSite31Physical.physicalFrame 39 n args] =
      F pairCode ![modelNumeral M 85,F pairCode ![l+l,p]] := by
  dsimp only
  let n := (k+1)+1
  let e := physicalArgs args
  let f := F sourceFileCode args
  let p := F ones ![e 0+1,F (fileCode 9) (fun i => e i.succ)]
  have hf : f=p+p := by rw [show f = F (fileCode 10) e from modelSourceFile args,modelFileSucc,modelBlock]
  have hcomm (t a : M) : F ones ![t,(1 : M)+(a+a)] = F ones ![t+1,a] := by
    have hadd : (1 : M)+(a+a) = a+a+1 := by ac_rfl
    rw [hadd,PA194OnesCommute.modelOnesCommute]
    change _ = F ones ![F addCode ![t,F oneCode Fin.elim0],a]
    rw [modelAddOne,modelOnesSucc]
  have hv : F ones ![k,(1 : M)+(((1 : M)+(f+f))+((1 : M)+(f+f)))] = F ones ![n,f] := by
    dsimp only [n]
    rw [hcomm,hcomm]
  have h := PA194Site39SecondTo60.to60 k args
  dsimp only at h
  rw [hv,hf] at h
  have loop60 (a b : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 60,F pairCode ![a,b+b+1]]) =
      F pairCode ![modelNumeral M 60,F pairCode ![a+a+1,b]] := by
    have hh := rightOne 60 1 60 (by decide) (by decide +kernel) a b
    simpa only [modelNumeralOne] using hh
  have hs := PA194GenericRightScan.modelFullScan 60 loop60 n (modelNumeral M 12908) (p+p)
  have he := rightZero 60 0 85 (by decide) (by decide +kernel) (F ones ![n,modelNumeral M 12908]) p
  simp only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] at he
  have he1 : F PA194Stepper.stepper ![n+1,F pairCode ![modelNumeral M 60,F pairCode ![modelNumeral M 12908,F ones ![n,p+p]]]] =
      F pairCode ![modelNumeral M 85,F pairCode ![F ones ![n,modelNumeral M 12908]+F ones ![n,modelNumeral M 12908],p]] := by
    rw [show n+1 = F Code.succ (fun _ => n) from modelAddOne _,PA194Stepper.modelStepperSucc,hs,he]
  rw [PA194StepperCompose.modelStepperCompose,h,he1]
#print axioms to85
end models
end PA194Site39SecondTo85
