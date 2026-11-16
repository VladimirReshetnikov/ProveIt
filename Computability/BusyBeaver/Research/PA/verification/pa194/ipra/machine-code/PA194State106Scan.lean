import PA194GenericRightScan
import PA194RightRows
import PA194StepperCompose
set_option autoImplicit false
namespace PA194State106Scan
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194RightRows PRAModelIOpenPairing TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
/-- State 106 preserves an arbitrary model-length one-run, then moves right
across a zero into state 71. -/
theorem scanExit (n l r : M) :
    let a := F ones ![n,l]
    F PA194Stepper.stepper ![n+1,F pairCode ![modelNumeral M 106,F pairCode ![l,F ones ![n,r+r]]]] =
    F pairCode ![modelNumeral M 71,F pairCode ![a+a,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  have hloop (a b : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 106,F pairCode ![a,b+b+1]]) =
      F pairCode ![modelNumeral M 106,F pairCode ![a+a+1,b]] := by
    have h := rightOne 106 1 106 (by decide) (by decide +kernel) a b
    simpa only [PA194StateOne.modelNumeralOne] using h
  have hs := PA194GenericRightScan.modelFullScan 106 hloop n l (r+r)
  have hx := rightZero 106 0 71 (by decide) (by decide +kernel) (F ones ![n,l]) r
  simp only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] at hx
  change F PA194Stepper.stepper ![F addCode ![n,F oneCode Fin.elim0],_] = _
  rw [modelAddOne,PA194Stepper.modelStepperSucc,hs,hx]
#print axioms scanExit
end models
end PA194State106Scan
