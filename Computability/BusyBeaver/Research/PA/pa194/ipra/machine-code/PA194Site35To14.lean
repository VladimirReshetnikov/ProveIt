import PA194Site35SecondTo71
import PA194HalfFileSixWithTail
import PA194OnesCommute
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site35To14
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

def vec (k : M) (args : Fin 11 → M) : Fin 12 → M := Fin.cases (k+1) (physicalArgs args)
noncomputable def lefts (k : M) (args : Fin 11 → M) : Fin 7 → M :=
  let e := vec k args
  let x1 := F ones ![e 0+1,modelNumeral M 804]
  let l1 := x1+x1
  let x2 := F ones ![e 1+1,l1]
  let l2 := x2+x2
  let x3 := F ones ![e 2+1,l2]
  let l3 := x3+x3
  let x4 := F ones ![e 3+1,l3]
  let l4 := x4+x4
  let x5 := F ones ![e 4+1,l4]
  let l5 := x5+x5
  let x6 := F ones ![e 5+1,l5]
  ![modelNumeral M 804,l1,l2,l3,l4,l5,x6+x6]
noncomputable def scanCost (k : M) (args : Fin 11 → M) : M :=
  let e := vec k args
  ((((((e 0+1)+1)+((e 1+1)+1))+((e 2+1)+1))+((e 3+1)+1))+((e 4+1)+1))+((e 5+1)+1)
noncomputable def clock (k : M) (args : Fin 11 → M) : M :=
  let n := (k+1)+1
  let c := F addCode ![F addCode ![modelNumeral M 10,n+1],(1 : M)]
  let first := F addCode ![F addCode ![c,(k+1)+1],modelNumeral M 24]
  F addCode ![F addCode ![first,modelNumeral M 9],scanCost k args]

theorem to14 (k : M) (args : Fin 11 → M) :
    let e := vec k args
    let es : Fin 6 → M := fun i => e ⟨i.val+6,by omega⟩
    let r := F ones ![es 0+1,F (fileCode 4) (fun i => es i.succ)]
    F PA194Stepper.stepper ![clock k args,PA194SourceSite31Physical.physicalFrame 35 ((k+1)+1) args] =
      F pairCode ![modelNumeral M 14,F pairCode ![lefts k args 6,r]] := by
  dsimp only
  let e := vec k args
  let es : Fin 6 → M := fun i => e ⟨i.val+6,by omega⟩
  let f := F sourceFileCode args
  let p := F ones ![(k+1)+1,f]
  have hp : F (fileCode 11) e = p+p := by
    dsimp only [p,e,vec]
    rw [modelFileSucc,modelBlock]
    change F ones ![(k+1)+1,F (fileCode 10) (physicalArgs args)] + F ones ![(k+1)+1,F (fileCode 10) (physicalArgs args)] = _
    rw [←modelSourceFile]
  have hcomm (t a : M) : F ones ![t,(1 : M)+(a+a)] = F ones ![t+1,a] := by
    have hadd : (1 : M)+(a+a) = a+a+1 := by ac_rfl
    rw [hadd,PA194OnesCommute.modelOnesCommute]
    change _ = F ones ![F addCode ![t,F oneCode Fin.elim0],a]
    rw [modelAddOne,modelOnesSucc]
  have hv : F ones ![k,(1 : M)+(((1 : M)+(f+f))+((1 : M)+(f+f)))] = p := by
    dsimp only [p]
    rw [hcomm,hcomm]
  have h := PA194Site35SecondTo71.to71 k args
  dsimp only at h
  rw [hv] at h
  have hs := (PA194HalfFileSixWithTail.scanSixExact 4 e (modelNumeral M 804) p hp).2
  dsimp only at hs
  change F PA194Stepper.stepper ![scanCost k args,F pairCode ![modelNumeral M 71,F pairCode ![modelNumeral M 804,p]]] =
      F pairCode ![modelNumeral M 14,F pairCode ![lefts k args 6,F ones ![es 0+1,F (fileCode 4) (fun i => es i.succ)]]] at hs
  dsimp only [clock]
  rw [PA194StepperCompose.modelStepperCompose,h,hs]
#print axioms to14
end models
end PA194Site35To14
