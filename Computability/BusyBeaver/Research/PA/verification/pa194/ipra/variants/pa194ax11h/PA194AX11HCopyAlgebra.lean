import PA194AX11HCandidateDrain
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
namespace PA194AX11HCopyAlgebra
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194ModelMPDrain
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

def mid (a : Fin 11 → M) : Fin 11 → M :=
 Function.update (Function.update (Function.update a 4 (0 : M)) 1 (a 1+a 4)) 6 (a 4)

theorem mid_eq (a : Fin 11 → M) (hX : a 6 = 0) :
    argsAfter a 4 [1,6] (a (location 4)) = mid a := by
  funext i
  fin_cases i <;> simp [argsAfter,location,tally,mid,subSelf,hX,
    PA194StateOne.modelNumeralOne,show modelNumeral M 0 = (0:M) from rfl]

theorem final_eq (a : Fin 11 → M) (hX : a 6 = 0) :
    argsAfter (mid a) 6 [4] ((mid a) (location 6)) = Function.update a 1 (a 1+a 4) := by
  funext i
  fin_cases i <;> simp [argsAfter,location,tally,mid,subSelf,hX,
    PA194StateOne.modelNumeralOne,show modelNumeral M 0 = (0:M) from rfl]

#print axioms mid_eq
#print axioms final_eq
end models
end PA194AX11HCopyAlgebra
