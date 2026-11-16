import PA194AX11HMPPrep
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194AX11HMPPrepValues
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PA194ModelMPPush PA194ModelMPField PA194ModelMPImp PA194ModelMPTransfer PA194ModelMPDrain
open PA194TargetCantor PA194MachineProjections
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

/-- Coordinate form of the exact ordinary MP comparison input. -/
theorem output_values (a : Fin 11 → M) (hx : a 6 = 0) (hy : a 7 = 0) :
    let r := PA194PausedPrep.result (pushed (fieldArgs a)) (a 1) (a 2)
    r 1 = 0 ∧ r 2 = a 2 ∧ r 3 = a 3 ∧
    r 4 = a 4 + F fixedFirst ![a 8] ∧ r 5 = a 5 ∧
    r 6 = impValue (a 1) (a 4 + F fixedFirst ![a 8]) ∧ r 7 = 0 ∧
    r 8 = F fixedSecond ![a 8] := by
  simp [PA194PausedPrep.result,implicationArgs,transferArgs,location,pushed,fieldArgs,hx,hy]

#print axioms output_values
end models
end PA194AX11HMPPrepValues
