import PA194Site35SecondTo17
import PA194Site35SecondReturn
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site35SecondPass
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation PA194RegisterFile BinaryTapeCodes TableDispatch PA194Path27Header PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PA194BinaryDouble PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem secondPass (k : M) (args : Fin 11 → M) :
    let out := PA194Site35SecondTo17.output k args
    F PA194Stepper.stepper ![F addCode ![F addCode ![F addCode ![PA194Site35To14.clock k args,modelNumeral M 3],PA194Site35SecondTo17.backCost k args],modelNumeral M 25],
      PA194SourceSite31Physical.physicalFrame 35 ((k+1)+1) args] =
      F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),modelWord (PA194SourceProgram.path 35) (out+out)]] := by
  dsimp only
  let out := PA194Site35SecondTo17.output k args
  have h17 := PA194Site35SecondTo17.to17 k args
  dsimp only at h17
  have hr := PA194Site35SecondReturn.returnWord out
  have hw : modelWord [true,false,false,true,false,false,true,false,false] out =
      modelWord (PA194SourceProgram.path 35) (out+out) := by
    rw [PA194Site34PositivePath.path35]
    simp only [modelWord,Bool.false_eq_true,↓reduceIte,Bool.true_eq_false]
  rw [hw] at hr
  simp only [modelNumeralOne,modelWord,Bool.false_eq_true,↓reduceIte,Bool.true_eq_false] at hr
  rw [PA194StepperCompose.modelStepperCompose,h17,hr]
#print axioms secondPass
end models
end PA194Site35SecondPass
