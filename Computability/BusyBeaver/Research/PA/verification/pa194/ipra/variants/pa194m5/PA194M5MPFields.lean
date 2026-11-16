import PA194M5MPCommand
set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false
namespace PA194M5MPFields
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PA194SchedulerFetchPositive PA194ProgramDrain PA194M5MPCommand PA194ModelMPField
open PA194MachineProjections
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
theorem resultFields (a : Fin 11 → M) :
    let b := result a
    let d := a 4 + F fixedFirst ![a 8]
    let ok := PA194ProgramCons.implicationValue 5 (a 1) d = a 5
    b 0 = a 0 ∧ b 1 = (if ok then d else 0) ∧
    b 2 = (if ok then cantor 0 (a 2) else a 2) ∧
    b 3 = a 3 ∧ b 4 = d ∧ b 5 = 0 ∧
    b 6 = a 6 ∧ b 7 = a 7 ∧ b 8 = F fixedSecond ![a 8] := by
  classical
  simp [result,fieldArgs]
#print axioms resultFields
end models
end PA194M5MPFields
