import PA194AX11HAXTail
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194AX11HAXTailValues
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PA194ModelMPPush PA194ModelMPField PA194ModelMPImp PA194ModelMPTransfer PA194ModelMPDrain
open PA194MachineProjections PA194AX11HAXTail
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

/-- Register coordinates after the successful AX fall-through return. -/
theorem tail_values (a : Fin 11 → M) (hx : a 6 = 0) (hy : a 7 = 0) :
    let b := PA194ModelMPCompare.values (compareInput a) 0 0
    b 0 = a 0 ∧ b 1 = 0 ∧ b 2 = cantor (a 1) (a 2) ∧ b 3 = a 3 ∧
    b 4 = a 4 + F fixedFirst ![a 8] ∧ b 5 = 0 ∧ b 6 = 0 ∧ b 7 = 0 ∧
    b 8 = F fixedSecond ![a 8] := by
  simp [PA194ModelMPCompare.values,compareInput,PA194PausedPrep.result,implicationArgs,
    transferArgs,location,pushed,fieldArgs,hx,hy]

#print axioms tail_values
end models
end PA194AX11HAXTailValues
