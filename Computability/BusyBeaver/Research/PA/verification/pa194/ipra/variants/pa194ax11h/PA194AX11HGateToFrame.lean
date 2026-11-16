import PA194AX11HGateExact
import PA194AX11HAXTailFrame
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194AX11HGateToFrame
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194IteratedSimulation
open PA194ModelAXGate PA194AX11HAXTailFrame
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

/-- Candidate AX gate and inserted tail execute to the exact next frame. -/
theorem gate_to_frame (a : Fin 11 → M) (tail z l : M)
    (hx : a 6 = 0) (hy : a 7 = 0) (hstream : a 8 = cantor z l) :
    ∃ n : M, 0 < n ∧ F (iterate PA194AX11HSource.step) ![n,sourceState 3519 a tail] =
      sourceState 25 (outputArgs (result a) z l) tail := by
  obtain ⟨m,hm⟩ := PA194AX11HGateExact.gate a tail hx hy
  have h3 : result a 3 = 0 := resultClears a 3 (by simp)
  have h4 : result a 4 = 0 := resultClears a 4 (by simp)
  have h5 : result a 5 = 0 := resultClears a 5 (by simp)
  have h6 : result a 6 = 0 := resultClears a 6 (by simp)
  have h7 : result a 7 = 0 := resultClears a 7 (by simp)
  have hs : result a 8 = cantor z l := by rw [resultKeeps a 8 (by simp),hstream]
  obtain ⟨n,hn,ht⟩ := ax_tail_frame (result a) tail z l h3 h4 h5 h6 h7 hs
  refine ⟨m+n,lt_of_lt_of_le hn ?_,?_⟩
  · simpa [zero_add] using add_le_add (zero_le : (0 : M) ≤ m) (le_refl n)
  · rw [PA194ControllerRunAdd.iterateAdd,hm,ht]
#print axioms gate_to_frame
end models
end PA194AX11HGateToFrame
