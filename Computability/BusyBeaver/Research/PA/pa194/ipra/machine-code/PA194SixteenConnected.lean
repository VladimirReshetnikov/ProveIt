import PA194FifteenExitComposition
import PA194SixteenScanInvariant
import PA194StepperCompose
set_option autoImplicit false
namespace PA194SixteenConnected
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble
open BinaryTapeCodes PA194FifteenExitComposition
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelConnectedSixteen (n m p l r : M) :
    let v := F ones ![p,l]
    let u := F zeros ![n,F zeros ![m,1+(r+r)+(r+r)]]
    F PA194Stepper.stepper ![((((((((n+1)+(m+1))+1)+1)+m)+n)+1)+1)+p,
      F pairCode ![TableDispatch.modelNumeral M 12,
        F pairCode ![(v+v+1)+(v+v+1)+1,F zeros ![n,F ones ![m+1,r+r]+F ones ![m+1,r+r]+1]]]] =
    F pairCode ![TableDispatch.modelNumeral M 16,
      F pairCode ![l,F ones ![p+1,1+(u+u)+(u+u)]]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let v := F ones ![p,l]
  let u := F zeros ![n,F zeros ![m,1+(r+r)+(r+r)]]
  let t := ((((((n+1)+(m+1))+1)+1)+m)+n)+1+1
  let initial := F pairCode ![TableDispatch.modelNumeral M 12,
    F pairCode ![(v+v+1)+(v+v+1)+1,F zeros ![n,F ones ![m+1,r+r]+F ones ![m+1,r+r]+1]]]
  have h := modelEnterSixteen n m (v+v+1) r
  dsimp only at h
  rw [(modelOdd v).1,(modelOdd v).2] at h
  have hshape (x : M) : (1 : M)+(1+1)+((x+x)+(x+x))+((x+x)+(x+x)) =
      (1+(x+x)+(x+x))+(1+(x+x)+(x+x))+1 := by
    simp only [add_assoc,add_comm,add_left_comm]
  rw [hshape] at h
  have hentry : F PA194Stepper.stepper ![t,initial] =
      F pairCode ![TableDispatch.modelNumeral M 16,
        F pairCode ![v,(1+(u+u)+(u+u))+(1+(u+u)+(u+u))+1]] := by
    simpa only [t,initial,u,v] using h
  change F PA194Stepper.stepper ![F addCode ![t,p],initial] = _
  rw [PA194StepperCompose.modelStepperCompose,hentry,PA194SixteenScanInvariant.modelFullScan]
#print axioms modelConnectedSixteen
end models
end PA194SixteenConnected
