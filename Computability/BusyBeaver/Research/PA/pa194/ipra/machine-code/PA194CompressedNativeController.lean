import PA194CompressedLiteralController
import PA194ExplicitEndpoint

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace PA194CompressedNativeController
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
    (M↓[language] ⊧ PA194ExplicitEndpoint.haltClassical) ↔
      ∃ n : M, F pc ![F run ![n,initialSource]] = modelNumeral M 3674 := by
  exact PA194ExplicitEndpoint.haltClassical_model_iff.trans
    (PA194CompressedLiteralController.endpoint checks)

#print axioms endpoint
end models
end PA194CompressedNativeController
