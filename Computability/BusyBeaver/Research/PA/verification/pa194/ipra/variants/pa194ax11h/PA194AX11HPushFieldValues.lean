import PA194AX11HPushField
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194AX11HPushFieldValues
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194ModelMPPush PA194ModelMPField PA194MachineProjections
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

/-- Coordinate form of the file produced by the AX-tail push and MP field reader. -/
theorem output_values (a : Fin 11 → M) :
    fieldArgs (pushed a) 1 = 0 ∧
    fieldArgs (pushed a) 2 = cantor (a 1) (a 2) ∧
    fieldArgs (pushed a) 4 = a 4 + F fixedFirst ![a 8] ∧
    fieldArgs (pushed a) 6 = a 6 ∧
    fieldArgs (pushed a) 7 = a 7 ∧
    fieldArgs (pushed a) 8 = F fixedSecond ![a 8] := by
  simp [fieldArgs,pushed]

#print axioms output_values
end models
end PA194AX11HPushFieldValues
