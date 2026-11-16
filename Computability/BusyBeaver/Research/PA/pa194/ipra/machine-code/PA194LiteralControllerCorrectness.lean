import PA194FoldedAllCoverage
import PA194CompressedLiteralController

set_option autoImplicit false

namespace PA194LiteralControllerCorrectness
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194CompressedStartup

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

/-- Literal PA194 halting is equivalent to halting of the exact finite source
controller in every PRA model whose arithmetic reduct satisfies IΣ₁. -/
theorem endpoint :
    (∃ t : M, ¬ pi₁ (F PackedClock.clock (fun _ => t)) < modelNumeral M 194) ↔
      ∃ n : M, F pc ![F run ![n,initialSource]] = modelNumeral M 3674 :=
  PA194CompressedLiteralController.endpoint PA194FoldedAllCoverage.all

#print axioms endpoint
end models
end PA194LiteralControllerCorrectness
