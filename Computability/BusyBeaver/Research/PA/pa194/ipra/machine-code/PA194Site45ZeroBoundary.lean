import PA194Site45ZeroRollback
import PA194RollbackCell
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site45ZeroBoundary
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation PA194RegisterFile BinaryTapeCodes TableDispatch PA194FiniteControls PA194UnaryRuns PA194StateOne PA194BinaryDouble PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem zeroToBoundary (k : M) (args : Fin 11 → M) (hz : args 6 = (0 : M)) :
    let f := F sourceFileCode args
    let w := F ones ![k+1,f]
    F PA194Stepper.stepper ![F addCode ![PA194Site45ZeroRollback.cost args,k+1],
      PA194Site45Branch.runTo4 k args] =
      F pairCode ![modelNumeral M 11,F pairCode ![modelNumeral M 204,w+w]] := by
  dsimp only
  let scan := F ones ![k,modelNumeral M 408]
  let f := F sourceFileCode args
  let w := F ones ![k+1,f]
  have hb : PA194Site45ZeroRollback.before k = scan+scan+1 := by
    dsimp only [PA194Site45ZeroRollback.before,scan]
    change F ones ![F addCode ![k,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelOnesSucc]
  have h := PA194Site45ZeroRollback.zeroRollback k args hz
  rw [hb,(modelOdd scan).1,(modelOdd scan).2] at h
  have hstart : F PA194Stepper.stepper ![PA194Site45ZeroRollback.cost args,PA194Site45Branch.runTo4 k args] =
      F pairCode ![modelNumeral M 11,F pairCode ![scan,f+f+1]] := by
    convert h using 1 <;> simp only [f,add_assoc,add_comm,add_left_comm]
  have h800 : modelNumeral M 204+modelNumeral M 204 = modelNumeral M 408 := by rw [←modelNumeralAdd]
  have hr := PA194RollbackCell.modelRollbackBoundary k (modelNumeral M 204) f
  rw [h800] at hr
  change F PA194Stepper.stepper ![k+1,F pairCode ![modelNumeral M 11,F pairCode ![scan,f+f+1]]] =
    F pairCode ![modelNumeral M 11,F pairCode ![modelNumeral M 204,w+w]] at hr
  rw [PA194StepperCompose.modelStepperCompose,hstart,hr]
#print axioms zeroToBoundary
end models
end PA194Site45ZeroBoundary
