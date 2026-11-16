import PA194M5Controller
import PA194M5Coverage

set_option autoImplicit false

namespace PA194M5PhysicalFinal
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode (pc)
open PA194CompressedStartup (initialSource)
open PA194IteratedSimulation (iterate)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem halt_iff_site10 :
    (∃ t : M, π₁ (ConPA.Machine.run PA194M5Data.table t) = (194 : M)) ↔
      ∃ n : M, F pc ![F (iterate (PA194ProgramControl.step PA194M5Program.program)) ![n,initialSource]] = modelNumeral M 10 :=
  PA194M5Controller.halt_iff_site10 PA194M5Coverage.checked

#print axioms halt_iff_site10
end models
end PA194M5PhysicalFinal
