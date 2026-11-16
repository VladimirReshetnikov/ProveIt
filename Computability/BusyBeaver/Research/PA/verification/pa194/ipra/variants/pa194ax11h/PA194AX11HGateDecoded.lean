import PA194AX11HGateToFrame
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194AX11HGateDecoded
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194IteratedSimulation
open PA194ModelAXGate PA194AX11HAXTailFrame PA194MachineProjections
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

/-- Gate and tail from arbitrary stream contents; both stream components are decoded internally. -/
theorem gate_to_frame (a : Fin 11 → M) (tail : M) (hx : a 6 = 0) (hy : a 7 = 0) :
    ∃ n : M, 0 < n ∧ F (iterate PA194AX11HSource.step) ![n,sourceState 3519 a tail] =
      sourceState 25 ![a 0,0,cantor (result a 1) (a 2),0,F fixedFirst ![a 8],0,0,0,F fixedSecond ![a 8],0,0] tail := by
  let z := F fixedFirst ![a 8]
  let l := F fixedSecond ![a 8]
  have hs : a 8 = cantor z l := by simp [z,l,fixedFirst_model,fixedSecond_model]
  obtain ⟨n,hn,ht⟩ := PA194AX11HGateToFrame.gate_to_frame a tail z l hx hy hs
  have h0 := resultKeeps a 0 (by simp)
  have h2 := resultKeeps a 2 (by simp)
  have he : outputArgs (result a) z l = ![a 0,0,cantor (result a 1) (a 2),0,z,0,0,0,l,0,0] := by
    funext i
    fin_cases i <;> simp [outputArgs,h0,h2]
  exact ⟨n,hn,by simpa [z,l,he] using ht⟩
#print axioms gate_to_frame
end models
end PA194AX11HGateDecoded
