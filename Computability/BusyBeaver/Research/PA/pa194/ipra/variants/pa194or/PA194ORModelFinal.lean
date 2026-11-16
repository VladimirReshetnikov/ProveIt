import PA194ORCoverage
import PA194ORController

set_option autoImplicit false

namespace PA194ORModelFinal
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PA194SourceControllerCode TableDispatch

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The OR blank run and the shared source controller agree on halting at
arbitrary model-valued clocks. -/
theorem halt_iff_controller :
    (∃ t : M, π₁ (ConPA.Machine.run PA194ORData.table t) = (194 : M)) ↔
      ∃ n : M, F pc ![F run ![n,PA194CompressedStartup.initialSource]] = modelNumeral M 3674 :=
  PA194ORController.halt_iff_controller PA194ORCoverage.checked (PA194ORController.literalBoxes _)

#print axioms halt_iff_controller
end models
end PA194ORModelFinal
