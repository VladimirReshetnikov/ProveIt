import PA194HeaderTo61
import PA194State61OddRoute
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194OddHeaderTo106
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194ZeroRuns PA194HeaderTo61 PA194State61OddRoute
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
theorem oddHeaderTo106 (u k r : M) :
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    let xx := h+h+1
    let ll := (xx+xx)+(xx+xx)+1
    let a0 := ll+ll+1
    let a1 := a0+a0+1
    let a2 := a1+a1+1
    let a3 := a2+a2+1
    let s0 := (r+r)+(r+r)+1
    let s := s0+s0+1
    let b := F ones ![k,s]
    let w := b+b+1
    let p := F ones ![modelNumeral M 3,(1 : M)+(w+w)+(w+w)]
    let v := p+p+1
    let l := F ones ![k,(a3+a3)+(a3+a3)]
    let l1 := l+l+1
    let l2 := l1+l1+1
    let c := (((modelNumeral M 1+1)+1)+1)+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![(((c+modelNumeral M 3)+modelNumeral M 4)+1)+((modelNumeral M 3+k)+modelNumeral M 3),
      F pairCode ![modelNumeral M 17,F pairCode ![h,(v+v)+(v+v)+1]]] =
    F pairCode ![modelNumeral M 106,F pairCode ![l2+l2,r]] := by
  dsimp only
  have h61 := nextHeaderTo61 u (F ones ![k,((r+r)+(r+r)+1)+((r+r)+(r+r)+1)+1] +
      F ones ![k,((r+r)+(r+r)+1)+((r+r)+(r+r)+1)+1] + 1)
  dsimp only at h61
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,h61,oddTo106]
#print axioms oddHeaderTo106
end models
end PA194OddHeaderTo106
