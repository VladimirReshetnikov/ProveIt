import PA194AX11HMPPositive
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194AX11HMPFields
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion PRASubAddition TableDispatch
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194ModelMPImp PA194TargetCantor
open PA194MachineProjections
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem outputFields (a : Fin 11 → M) :
    let b := PA194AX11HMPSource.output a
    let d := a 4 + F fixedFirst ![a 8]
    b 0 = a 0 ∧ b 1 = (if impValue (a 1) d = a 5 then d else 0) ∧
    b 2 = a 2 ∧ b 3 = a 3 ∧ b 4 = d ∧ b 5 = 0 ∧
    b 6 = 0 ∧ b 7 = a 7 ∧ b 8 = F fixedSecond ![a 8] ∧ b 9 = a 9 ∧ b 10 = a 10 := by
  classical
  simp [PA194AX11HMPSource.output]

#print axioms outputFields
end models
end PA194AX11HMPFields
