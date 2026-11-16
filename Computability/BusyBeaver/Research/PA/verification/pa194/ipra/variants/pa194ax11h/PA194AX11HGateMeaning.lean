import PA194AX11HGateDecoded
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194AX11HGateMeaning
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194IteratedSimulation
open PA194ModelAXGate PA194MachineProjections PA194TargetGate
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

/-- If the preceding AX body supplies the bundle, the returned stack contains the AX gate. -/
theorem gate_to_frame_ax (a : Fin 11 → M) (tail : M)
    (hx : a 6 = 0) (hy : a 7 = 0) (ht : a 1 = oldBundleValue (a 5) (a 4) (a 3)) :
    ∃ n : M, 0 < n ∧ F (iterate PA194AX11HSource.step) ![n,sourceState 3519 a tail] =
      sourceState 25 ![a 0,0,cantor (PA194MachineStack.axTop (a 5) (a 4) (a 3)) (a 2),0,
        F fixedFirst ![a 8],0,0,0,F fixedSecond ![a 8],0,0] tail := by
  have h := PA194AX11HGateDecoded.gate_to_frame a tail hx hy
  rwa [resultTop a ht] at h
#print axioms gate_to_frame_ax
end models
end PA194AX11HGateMeaning
