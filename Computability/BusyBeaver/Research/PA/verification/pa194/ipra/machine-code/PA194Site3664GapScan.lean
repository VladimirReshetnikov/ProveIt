import PA194Site3664SecondTo85
import PA194HalfFileWithTail
import PA194RightRows
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site3664GapScan
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation BinaryTapeCodes TableDispatch PA194Path27Header PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PA194BinaryDouble PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem scan (k l f r : M) (hf : f = r+r) :
    let a := F ones ![k,l]
    F PA194Stepper.stepper ![((k+1)+1)+1,F pairCode ![modelNumeral M 85,F pairCode ![l,F ones ![k,(1 : M)+(((1 : M)+(f+f))+((1 : M)+(f+f)))]]]] =
      F pairCode ![modelNumeral M 106,F pairCode ![(a+a+1+(a+a+1)+1)+(a+a+1+(a+a+1)+1),r]] := by
  dsimp only
  have loop95 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 85,F pairCode ![x,y+y+1]]) = F pairCode ![modelNumeral M 85,F pairCode ![x+x+1,y]] := by
    have h := PA194RightRows.rightOne 85 1 85 (by decide) (by decide +kernel) x y
    simpa only [PA194StateOne.modelNumeralOne] using h
  have exit95 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 85,F pairCode ![x,y+y]]) = F pairCode ![modelNumeral M 106,F pairCode ![x+x,y]] := by
    have h := PA194RightRows.rightZero 85 0 106 (by decide) (by decide +kernel) x y
    simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using h
  let d := (1 : M)+(f+f)
  have hs := PA194GenericRightScan.modelFullScan 85 loop95 k l ((1 : M)+(d+d))
  have ha : (1 : M)+(d+d) = d+d+1 := by ac_rfl
  rw [ha] at hs ⊢
  change F PA194Stepper.stepper ![F addCode ![F addCode ![F addCode ![k,F oneCode Fin.elim0],F oneCode Fin.elim0],F oneCode Fin.elim0],_] = _
  rw [modelAddOne,modelAddOne,modelAddOne,PA194Stepper.modelStepperSucc,PA194Stepper.modelStepperSucc,PA194Stepper.modelStepperSucc,hs,loop95]
  rw [show d = f+f+1 by dsimp only [d]; ac_rfl,loop95,hf,exit95]
#print axioms scan
end models
end PA194Site3664GapScan
