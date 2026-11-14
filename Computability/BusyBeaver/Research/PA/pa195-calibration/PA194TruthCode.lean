import PA194NumeralCode
import PA194EqAtomCode

/-! The concrete numeric Foundation truth-syntax constructor. -/
set_option autoImplicit false
namespace PA194TruthCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing PA194NumeralCode

def truthCode : Code 1 := numeralCode 1 7

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem modelTruthValue (x : M) : F truthCode (fun _ => x) = pair 2 0 + 1 := by
  rw [truthCode, modelNumeralCode]
  norm_num [pair]

theorem modelTruthInternal [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (x : M) :
    F truthCode (fun _ => x) = (qqVerum : M) := by
  rw [modelTruthValue,qqVerum]

#print axioms modelTruthValue
#print axioms modelTruthInternal
end models
end PA194TruthCode
