import PA194Site34SecondTo17
import PA194Site34SecondReturn
import PA194Path34Header
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site34SecondPass
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
    let e := physicalArgs args
    let tail := F (fileCode 8) (fun i => e i.succ.succ)
    let u := F ones ![e 1,tail]
    let c := (u+u)+(u+u)
    let w := F ones ![e 0,(1 : M)+c+c]
    let out := F ones ![k+1,(1 : M)+(w+w)+(w+w)]
    let back := (e 0+1)+(((k+1)+1)+1)
    F PA194Stepper.stepper ![F addCode ![F addCode ![F addCode ![PA194Site34SecondTo17.to14Clock k args,modelNumeral M 3],back],modelNumeral M 24],
      PA194SourceSite31Physical.physicalFrame 34 ((k+1)+1) args] =
      F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),modelWord (PA194SourceProgram.path 34) (out+out)]] := by
  dsimp only
  let e := physicalArgs args
  let tail := F (fileCode 8) (fun i => e i.succ.succ)
  let u := F ones ![e 1,tail]
  let c := (u+u)+(u+u)
  let w := F ones ![e 0,(1 : M)+c+c]
  let out := F ones ![k+1,(1 : M)+(w+w)+(w+w)]
  have h17 := PA194Site34SecondTo17.to17 k args
  dsimp only at h17
  have hr := PA194Site34SecondReturn.returnWord out
  have hw : modelWord [true,false,false,true,false,false,false,false] out =
      modelWord (PA194SourceProgram.path 34) (out+out) := by
    rw [PA194Path34Header.path34]
    simp only [modelWord,Bool.false_eq_true,↓reduceIte,Bool.true_eq_false]
  rw [hw] at hr
  simp only [modelNumeralOne] at hr
  change F PA194Stepper.stepper ![modelNumeral M 24,F pairCode ![modelNumeral M 17,
      F pairCode ![modelNumeral M 100,(out+out)+(out+out)]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),modelWord (PA194SourceProgram.path 34) (out+out)]] at hr
  rw [PA194StepperCompose.modelStepperCompose,h17,hr]
#print axioms secondPass
end models
end PA194Site34SecondPass
