import PA194GenericRightScan
import PA194RightRows
import PA194OnesCommute
import PA194StepperCompose
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site27Scan106
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RightRows PA194UnaryRuns PA194OnesCommute PA194StateOne PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem onesExtendTwo (k x : M) :
    F ones ![k,(x+x+1)+(x+x+1)+1] = F ones ![(k+1)+1,x] := by
  rw [modelOnesCommute,modelOnesCommute]
  change _ = F ones ![F addCode ![k+1,F oneCode Fin.elim0],x]
  rw [modelAddOne,modelOnesSucc]
  change _ = F ones ![F addCode ![k,F oneCode Fin.elim0],x] + F ones ![F addCode ![k,F oneCode Fin.elim0],x]+1
  rw [modelAddOne,modelOnesSucc]

theorem scan106To71 (k l p : M) :
    let x := p+p
    let t := (1 : M)+(1+1)+((p+p)+(p+p))+((p+p)+(p+p))
    let n := (k+1)+1
    let a := F ones ![n,l]
    F PA194Stepper.stepper ![n+1,F pairCode ![modelNumeral M 106,F pairCode ![l,F ones ![k,t]]]] =
    F pairCode ![modelNumeral M 71,F pairCode ![a+a,p]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let x := p+p
  let n := (k+1)+1
  let a := F ones ![n,l]
  have ht : (1 : M)+(1+1)+((p+p)+(p+p))+((p+p)+(p+p)) = (x+x+1)+(x+x+1)+1 := by
    dsimp [x]; simp only [add_assoc,add_comm,add_left_comm]
  rw [ht,onesExtendTwo]
  have hloop (a b : M) : F PackedClock.encodedStep
      (fun _ => F pairCode ![modelNumeral M 106,F pairCode ![a,b+b+1]]) =
      F pairCode ![modelNumeral M 106,F pairCode ![a+a+1,b]] := by
    have h := rightOne 106 1 106 (by decide) (by decide +kernel) a b
    simpa only [show modelNumeral M 1 = (1 : M) from modelNumeralOne] using h
  have hs := PA194GenericRightScan.modelFullScan 106 hloop n l x
  have hout := rightZero 106 0 71 (by decide) (by decide +kernel) a p
  simp only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] at hout
  change F PA194Stepper.stepper ![F addCode ![n,F oneCode Fin.elim0],_] = _
  rw [modelAddOne,PA194Stepper.modelStepperSucc,hs,hout]
#print axioms onesExtendTwo
#print axioms scan106To71
end models
end PA194Site27Scan106
