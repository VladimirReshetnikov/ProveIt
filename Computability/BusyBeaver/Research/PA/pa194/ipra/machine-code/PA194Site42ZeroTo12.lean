import PA194Site42ZeroBoundary
import PA194Site42ZeroBoundaryTo12
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site42ZeroTo12
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

theorem zeroTo12 (k : M) (args : Fin 11 → M) (hz : args 7 = (0 : M)) :
    let f := F sourceFileCode args
    let w := F ones ![k+1,f]
    let d := w+w+1
    F PA194Stepper.stepper ![F addCode ![F addCode ![PA194Site42ZeroRollback.cost args,k+1],modelNumeral M 5],
      PA194Site42Branch.runTo4 k args] =
      F pairCode ![modelNumeral M 12,F pairCode ![modelNumeral M 51,((d+d)+(d+d))+((d+d)+(d+d))]] := by
  dsimp only
  let w := F ones ![k+1,F sourceFileCode args]
  have h := PA194Site42ZeroBoundary.zeroToBoundary k args hz
  dsimp only at h
  have h12 := PA194Site42ZeroBoundaryTo12.fiveRows w
  simp only [modelWord,Bool.false_eq_true,↓reduceIte,Bool.true_eq_false] at h12
  rw [PA194StepperCompose.modelStepperCompose,h,h12]
#print axioms zeroTo12
end models
end PA194Site42ZeroTo12
