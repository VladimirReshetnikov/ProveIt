import PA194PausedFirstHit
import PA194PausedPush

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
namespace PA194FirstActualPush
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194ModelMPPush
open PA194PausedSites PA194IteratedSimulation
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The first actual primary exit from the MP push has the exact pushed file. -/
theorem first_actual_push (a : Fin 11 → M) (tail : M) (hX : a 6 = 0) (hY : a 7 = 0) :
    ∃ n : M, F (iterate step) ![n,sourceState 3568 a tail] = sourceState 3587 (pushed a) tail ∧
      ∀ j < n, F pc ![F (iterate step) ![j,sourceState 3568 a tail]] ≠ modelNumeral M 3587 := by
  apply PA194PausedFirstHit.first_actual_exit PA194AX11HPushPaused.oldPaused 3587
  · exact PA194AX11HPushPaused.oldPaused_model
  · exact source_pc 3587 (pushed a) tail
  · exact PA194PausedPush.push a tail hX hY

#print axioms first_actual_push
end models
end PA194FirstActualPush
