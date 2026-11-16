import PA194Site32HeaderPass
import PA194Site29SecondDispatch
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site32MarkedTo60
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194Site32HeaderTo64 PA194Site29SecondDispatch PA194StateOne PRAModelIOpenPairing PA194Path27Header
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem markedTo60 (l u : M) :
    let a0 := l+l+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a5 := a4+a4+1
    let a6 := a5+a5+1
    let c12 := F addCode ![F addCode ![modelNumeral M 8,modelNumeral M 3],(1 : M)]
    F PA194Stepper.stepper ![F addCode ![c12,(1 : M)],
      F pairCode ![modelNumeral M 24,F pairCode ![l,modelWord (PA194SourceProgram.path 32) (u+u+1)]]] =
    F pairCode ![modelNumeral M 60,F pairCode ![(a6+a6)+(a6+a6),u]] := by
  dsimp only
  change F PA194Stepper.stepper ![F addCode ![F addCode ![F addCode ![modelNumeral M 8,modelNumeral M 3],F oneCode Fin.elim0],F oneCode Fin.elim0],_] = _
  have h := pathTo42 l (u+u+1)
  dsimp only at h
  change F PA194Stepper.stepper ![F addCode ![F addCode ![modelNumeral M 8,modelNumeral M 3],F oneCode Fin.elim0],_] = _ at h
  rw [modelAddOne,PA194Stepper.modelStepperSucc,h,row42one]
#print axioms markedTo60
end models
end PA194Site32MarkedTo60
