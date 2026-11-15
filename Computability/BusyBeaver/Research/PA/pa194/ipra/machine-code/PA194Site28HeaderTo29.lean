import PA194Path29Header
import PA194Site28ReturnHeader
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site28HeaderTo29
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194Site28ReturnHeader PA194Path29Header PA194ZeroRuns PA194UnaryRuns PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem headerTo29 (k p : M) :
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a5 := a4+a4
    let a6 := a5+a5+1
    let a7 := a6+a6
    let w := F ones ![k,(1 : M)+(p+p)+(p+p)]
    let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![modelNumeral M 2+(modelNumeral M 3+rc),
      F PA194Stepper.stepper ![(1 : M),
        F PA194Stepper.stepper ![((1 : M)+k)+modelNumeral M 3,
          F PA194Stepper.stepper ![((modelNumeral M 2+1)+k)+1,
            F PA194Stepper.stepper ![modelNumeral M 2,
              F pairCode ![modelNumeral M 7,F pairCode ![a7,(w+w)+(w+w)]]]]]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),
      PA194Path27Header.modelWord (PA194SourceProgram.path 29) (F zeros ![k+1,(1 : M)+(p+p)+(p+p)])]] := by
  have h := PA194Site28ReturnHeader.headerTo24 (M := M) k p
  have hid := PA194Path29Header.resultIsPath29 (M := M) k p
  dsimp only at h hid ⊢
  exact h.trans (congrArg (fun x => F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),x]]) hid)
#print axioms headerTo29
end models
end PA194Site28HeaderTo29
