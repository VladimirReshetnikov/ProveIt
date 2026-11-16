import PA194Site3671HeaderFinish
import PA194Site31ReturnHeader
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site3671HeaderReturn
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194Path27Header PA194UnaryRuns BinaryTapeCodes TableDispatch PA194Site28ReturnHeader PA194FirstThreeBlankTailTo16 PA194ZeroRuns PA194StateOne PA194FiniteControls PA194BinaryDouble PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem headerTo24 (k p : M) :
    let w := F ones ![k,(1 : M)+(p+p)+(p+p)]
    let z := F zeros ![k,(1 : M)+(p+p)+(p+p)]
    let r := (z+z)+(z+z)
    F PA194Stepper.stepper ![modelNumeral M 19,
      F PA194Stepper.stepper ![((1 : M)+k)+modelNumeral M 3,
        F PA194Stepper.stepper ![((modelNumeral M 2+1)+k)+1,
          F PA194Stepper.stepper ![modelNumeral M 2,
            F pairCode ![modelNumeral M 7,F pairCode ![modelNumeral M 14,(w+w)+(w+w)]]]]]] =
      F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),modelWord [true,true,true] r]] := by
  dsimp only
  let w := F ones ![k,(1 : M)+(p+p)+(p+p)]
  let z := F zeros ![k,(1 : M)+(p+p)+(p+p)]
  let r := (z+z)+(z+z)
  have h12 := twoTo12 (M := M) (modelNumeral M 7) w
  have h14 := scansTo14 (M := M) (modelNumeral M 7) k p
  have h16 := header14To16 (M := M) k (modelNumeral M 7) p
  dsimp only at h16
  have h402 : modelNumeral M 7+modelNumeral M 7 = modelNumeral M 14 := by rw [←modelNumeralAdd]
  have h201 : modelNumeral M 7 = modelNumeral M 3+modelNumeral M 3+1 := by rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  rw [h402] at h12 h14 h16
  rw [h201,(modelOdd (modelNumeral M 3)).1,(modelOdd (modelNumeral M 3)).2] at h16
  have hf := PA194Site3671HeaderFinish.returnWord r
  have hr : modelWord [true,true] r = (1 : M)+(1+1)+(r+r)+(r+r) := by
    simp only [modelWord,Bool.false_eq_true,↓reduceIte,Bool.true_eq_false]
    ac_rfl
  rw [hr] at hf
  simp only [modelNumeralOne] at hf
  rw [h12,h14,h16,hf]
#print axioms headerTo24
end models
end PA194Site3671HeaderReturn
