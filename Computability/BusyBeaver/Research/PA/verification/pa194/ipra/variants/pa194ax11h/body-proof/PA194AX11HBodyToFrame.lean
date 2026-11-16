import PA194AX11HBodyAll
import PA194AX11HGateMeaning
import PA194AXModelValues
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194AX11HBodyToFrame
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194IteratedSimulation
open PA194AX11HBodyCopy PA194ModelAXPlan PA194AXSymbolic PA194AXModelValues
open PA194MachineProjections PA194MachineStack
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

/-- The full candidate AX body and gate reach its exact next frame, conditional only on
finite row agreement with the primary AX body. -/
theorem body_to_frame (agree : BodyRowsAgree) (a : Fin 11 → M) (tail : M)
    (hx : a 6 = 0) (hy : a 7 = 0) :
    let b := bodyValues a
    ∃ n : M, 0 < n ∧ F (iterate PA194AX11HSource.step) ![n,sourceState 50 a tail] =
      sourceState 25 ![b 0,0,cantor (axTop (b 5) (b 4) (b 3)) (b 2),0,
        F fixedFirst ![b 8],0,0,0,F fixedSecond ![b 8],0,0] tail := by
  dsimp only
  let b := bodyValues a
  have hb := PA194AX11HBodyAll.body agree a tail hx hy
  rw [body_evaluation a hx hy] at hb
  obtain ⟨m,hm⟩ := hb
  have h6 : b 6 = 0 := rfl
  have h7 : b 7 = 0 := rfl
  have ht : b 1 = PA194TargetGate.oldBundleValue (b 5) (b 4) (b 3) := rfl
  obtain ⟨n,hn,hg⟩ := PA194AX11HGateMeaning.gate_to_frame_ax b tail h6 h7 ht
  refine ⟨m+n,lt_of_lt_of_le hn ?_,?_⟩
  · simpa [zero_add] using add_le_add (zero_le : (0 : M) ≤ m) (le_refl n)
  · rw [PA194ControllerRunAdd.iterateAdd,hm,hg]
#print axioms body_to_frame
end models
end PA194AX11HBodyToFrame
