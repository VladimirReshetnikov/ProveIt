import PA194Site27PositiveHeaderTo12
import PA194Site36PositiveReturn
import PA194Site32PositiveFile
import PA194Site27PositiveCell
import PA194Site27PositiveHeaderTo12
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site36PositiveTo12
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194StateOne PA194FiniteControls TableDispatch PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ReturnFileMeaning PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem positiveTo12 (k : M) (args : Fin 11 → M) (m : M) (hm : args 6 = m+1) :
    let f := F sourceFileCode (Function.update args 6 m)
    let w := F ones ![k+1,(1 : M)+f+f]
    let c := F addCode ![PA194Site32PositiveReturnExact.returnCost args,
      ((1 : M)+((k+1)+1))+modelNumeral M 3]
    F PA194Stepper.stepper ![c,PA194Site36Branch.runTo4 k args] =
      F pairCode ![modelNumeral M 12,F pairCode ![modelNumeral M 3225,(w+w)+(w+w)]] := by
  dsimp only
  let updated := Function.update args 6 m
  let v := physicalArgs updated
  let f := F sourceFileCode updated
  let p := F ones ![v 0+1,F (fileCode 9) (fun i => v i.succ)]
  have hf : f = p+p := by rw [show f = F (fileCode 10) v from modelSourceFile updated,modelFileSucc,modelBlock]
  have h := PA194Site36PositiveReturn.positiveReturn k args m hm
  have h12 := PA194Site27PositiveHeaderTo12.headerTo12 k (modelNumeral M 1612) p
  dsimp only at h12
  have n12896 : ((modelNumeral M 1612+modelNumeral M 1612)+(modelNumeral M 1612+modelNumeral M 1612))+((modelNumeral M 1612+modelNumeral M 1612)+(modelNumeral M 1612+modelNumeral M 1612)) = modelNumeral M 12896 := by
    repeat rw [←modelNumeralAdd]
  have n3225 : modelNumeral M 1612+modelNumeral M 1612+1 = modelNumeral M 3225 := by
    rw [←modelNumeralAdd,←modelNumeralOne,←modelNumeralAdd]
  rw [n12896,n3225,←hf] at h12
  have hsum : (1 : M)+f+f = (f+f)+1 := by simp only [add_assoc,add_comm,add_left_comm]
  rw [hsum]
  rw [PA194StepperCompose.modelStepperCompose,h,h12]
#print axioms positiveTo12
end models
end PA194Site36PositiveTo12
