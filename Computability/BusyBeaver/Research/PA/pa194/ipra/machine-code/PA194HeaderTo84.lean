import PA194HeaderTo61
import PA194State61Return
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194HeaderTo84
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble PA194HeaderTo61 PA194State61Return
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

theorem nextHeaderTo84 (u x : M) :
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    let xx := h+h+1
    let l := (xx+xx)+(xx+xx)+1
    let a0 := l+l+1
    let a1 := a0+a0+1
    let a2 := a1+a1+1
    let a3 := a2+a2+1
    let z := (x+x)+(x+x)
    let s := (1 : M)+(z+z)+(z+z)
    let p := F ones ![modelNumeral M 3,s]
    let w := p+p+1
    let c := (((modelNumeral M 1+1)+1)+1)+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![(((c+modelNumeral M 3)+modelNumeral M 4)+1)+modelNumeral M 10,
      F pairCode ![modelNumeral M 17,F pairCode ![h,(w+w)+(w+w)+1]]] =
    F pairCode ![modelNumeral M 84,F pairCode ![a3+a3,z]] := by
  dsimp only
  have h := nextHeaderTo61 u ((x+x)+(x+x))
  dsimp only at h
  change F PA194Stepper.stepper ![F addCode ![_,modelNumeral M 10],_] = _
  rw [PA194StepperCompose.modelStepperCompose,h,state61To84]
#print axioms nextHeaderTo84
end models
end PA194HeaderTo84
