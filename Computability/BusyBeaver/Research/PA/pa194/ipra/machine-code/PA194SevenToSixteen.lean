import PA194SevenReturnController
import PA194FifteenExitComposition
import PA194ZeroRuns
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194SevenToSixteen
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194RegisterFile PA194ZeroRuns PA194SevenReturnController
open PA194FifteenExitComposition PRAModelIOpenPairing TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem positiveFirstToSixteen (k a r : M) :
    let b := F block ![k+1,r+r]
    let n := modelNumeral M 2
    let u := F zeros ![n,F zeros ![k,1+(r+r)+(r+r)]]
    let c := (((((((n+1)+(k+1))+1)+1)+k)+n)+1)+1
    F PA194Stepper.stepper ![modelNumeral M 2+c,
      F pairCode ![modelNumeral M 7,F pairCode ![a+a,b+b]]] =
    F pairCode ![modelNumeral M 16,F pairCode ![F halfCode (fun _ => a),
      F parityCode (fun _ => a)+(1+1)+(u+u+(u+u))+(u+u+(u+u))]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let z := F ones ![k+1,r+r]
  have ho : F ones ![(k+1)+1,r+r] = z+z+1 := by
    change F ones ![F addCode ![k+1,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelOnesSucc]
  have hz (x : M) : F zeros ![modelNumeral M 2,x] = (x+x)+(x+x) := by
    rw [show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,modelZerosSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,modelZerosSucc]
    change (F zeros ![(0 : M),x]+F zeros ![(0 : M),x])+(F zeros ![(0 : M),x]+F zeros ![(0 : M),x]) = _
    rw [modelZerosZero]
  have hb : let b := F block ![k+1,r+r]; b+b = F zeros ![modelNumeral M 2,z+z+1] := by
    dsimp only
    rw [modelBlock,ho,hz]
  have hx := modelEnterSixteen (modelNumeral M 2) k a r
  dsimp only at hx
  rw [←hb] at hx
  change F PA194Stepper.stepper ![F addCode ![modelNumeral M 2,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,sevenToTwelve]
  exact hx
#print axioms positiveFirstToSixteen
end models
end PA194SevenToSixteen
