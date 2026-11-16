import PA194Site3671GapDispatch
import PA194Site3671To70Rows
import PA194LeftRows
import PA194LeftOneRows
import PA194LeftOneWriteOne
import PA194Site32ZeroPath
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site3671To70
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation BinaryTapeCodes TableDispatch PA194Path27Header PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PA194BinaryDouble PA194RightRows PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem positiveTo70 (gap : M) (args : Fin 11 → M) :
    let f := F sourceFileCode args
    let rest := F zeros ![gap,(1 : M)+(f+f)]
    F PA194Stepper.stepper ![modelNumeral M 8,PA194SourceSite31Physical.physicalFrame 3671 (gap+1) args] =
      F pairCode ![modelNumeral M 70,F pairCode ![modelNumeral M 28,rest]] := by
  dsimp only
  let f := F sourceFileCode args
  let rest := F zeros ![gap,(1 : M)+(f+f)]
  have h := PA194Site3671GapDispatch.positiveGap gap args
  dsimp only at h
  have hr := PA194Site3671To70Rows.prefixWord rest
  simp only [modelWord,Bool.false_eq_true,↓reduceIte] at hr
  nth_rewrite 1 [show modelNumeral M 8 = F addCode ![modelNumeral M 6,modelNumeral M 2] from by change modelNumeral M 8 = modelNumeral M 6+modelNumeral M 2; rw [←modelNumeralAdd]]
  rw [PA194StepperCompose.modelStepperCompose,h,hr]
#print axioms positiveTo70
end models
end PA194Site3671To70
