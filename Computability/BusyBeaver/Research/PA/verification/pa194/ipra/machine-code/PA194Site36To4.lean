import PA194Site36CarryFrom1
import PA194Site36To1
import PA194Site36MarkedFile
import PA194Site32CarryTo4
import PA194Site36SecondPass
import PA194Site36ThirdPrefix
import PA194Site36SecondTo17
import PA194Site36SecondReturn
import PA194Site36SecondTo14
import PA194FourteenOddTo16
import PA194Site35SixteenSixRuns
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site36To4
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194CarryFile PA194Path27Header PA194RegisterPermutation PA194RegisterFile BinaryTapeCodes TableDispatch PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PA194BinaryDouble PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem to4 (k : M) (args : Fin 11 → M) :
    let e := physicalArgs args
    let out := PA194Site36SecondTo17.output k args
    let v := physicalArgs args
    let sel := PA194Site36MarkedFile.selectedArgs args
    let tail := F (fileCode 1) (fun i => sel i.succ)
    let q := F ones ![sel 0,tail]
    let vec := PA194Site36MarkedFile.prefixArgs args
    let before := F ones ![k+1,modelNumeral M 12896]
    let left := F (PA194CarryFile.leftCode 8) (Fin.cases before vec)
    let z := left+left+1
    let cost := ((k+1)+F (PA194CarryFile.costCode 8) vec)+modelNumeral M 2
    F PA194Stepper.stepper ![cost,
    F PA194Stepper.stepper ![modelNumeral M 13,
    F PA194Stepper.stepper ![modelNumeral M 28,F PA194Stepper.stepper ![((k+1)+1)+1,
      F PA194Stepper.stepper ![(e 0+1)+1,
        F PA194Stepper.stepper ![(e 1+1)+1,
          F PA194Stepper.stepper ![PA194Site36SecondTo17.sixCost args,
            F PA194Stepper.stepper ![modelNumeral M 3,
              F PA194Stepper.stepper ![PA194Site36SecondTo14.clock k args,
                PA194SourceSite31Physical.physicalFrame 36 ((k+1)+1) args]]]]]]]]] =
      F pairCode ![modelNumeral M 4,F pairCode ![z+z,q]] := by
  dsimp only
  have h := PA194Site36To1.to1 k args
  dsimp only at h
  conv_rhs at h => rw [modelNumeralOne]
  have hc := PA194Site36CarryFrom1.carry k args
  dsimp only at hc
  rw [h]
  exact hc
#print axioms to4
end models
end PA194Site36To4
