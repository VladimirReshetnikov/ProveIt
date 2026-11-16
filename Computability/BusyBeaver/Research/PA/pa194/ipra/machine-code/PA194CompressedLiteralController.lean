import PA194CompressedSourceOrbit
import PA194CompressedControllerStep
import PA194CompressedStartup

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace PA194CompressedLiteralController
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing TableDispatch
open PA194CompressedSourceOrbit PA194CompressedControllerStep PA194CompressedStartup
open PA194SourceControllerCode PA194Stepper

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

/-- The exact native endpoint from the literal dense PA194 clock coincides
with controller halting from the decoded packed startup. -/
theorem endpoint (checks : AllContracts) :
    (∃ t : M, ¬ pi₁ (F PackedClock.clock (fun _ => t)) < modelNumeral M 194) ↔
      ∃ n : M, F pc ![F run ![n,initialSource]] = modelNumeral M 3674 := by
  have h := equivalent (initialSource : M) (0 : M) initialSpare initialAligned (advance checks initialSpare)
  constructor
  · rintro ⟨t,ht⟩
    apply h.mp
    refine ⟨t,?_⟩
    exact (modelStepperBlank t).symm ▸ ht
  · intro hn
    obtain ⟨t,ht⟩ := h.mpr hn
    exact ⟨t,modelStepperBlank t ▸ ht⟩

#print axioms endpoint
end models
end PA194CompressedLiteralController
