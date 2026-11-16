import PA194RegisterControllerEndpoint
import PA194P5Representative
import PA194P5BoxAgreement
import PA194P5Seed

set_option autoImplicit false

namespace PA194P5SourceEndpoint
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing TableDispatch PA194FiniteControls PA194StateOne
open PA194SourceControllerCode PA194CompressedStartup
open PA194P5Data PA194P5Allocation PA194P5Rows

def Covered : Prop := PA194RegisterControllerAdvance.AllContracts allocation machine

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

theorem endpoint (checks : Covered) :
    (∃ t : M, π₁ (ConPA.Machine.run table t) = (194 : M)) ↔
      ∃ n : M, F pc ![F run ![n, initialSource]] = modelNumeral M 3674 :=
  PA194RegisterControllerEndpoint.endpoint allocation rows rowCount machine denseControl
    rowAgreement rootControl haltControl PA194P5BoxAgreement.concreteBoxAgreement checks
    PA194P5Representative.checkHalt (56158 : M) PA194P5Seed.startup_root

#print axioms endpoint
end models
end PA194P5SourceEndpoint
