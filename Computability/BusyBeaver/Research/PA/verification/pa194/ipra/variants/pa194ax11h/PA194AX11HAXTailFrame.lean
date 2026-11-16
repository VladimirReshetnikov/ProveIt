import PA194AX11HAXTailValues
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194AX11HAXTailFrame
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PA194SourceControllerCode PA194SourceFetchLoop PA194SchedulerFetchPositive PA194IteratedSimulation
open PA194ModelMPCompare PA194MachineProjections PA194AX11HAXTail PA194AX11HAXTailValues PA194StateOne
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

def outputArgs (a : Fin 11 → M) (z l : M) : Fin 11 → M :=
  ![a 0,0,cantor (a 1) (a 2),0,z,0,0,0,l,0,0]

/-- With the AX gate frame, the tail returns the expected next scheduler frame. -/
theorem ax_tail_frame (a : Fin 11 → M) (tail z l : M)
    (h3 : a 3 = 0) (h4 : a 4 = 0) (h5 : a 5 = 0) (h6 : a 6 = 0) (h7 : a 7 = 0)
    (hstream : a 8 = cantor z l) :
    ∃ n : M, 0 < n ∧ F (iterate PA194AX11HSource.step) ![n,sourceState 3553 a tail] =
      sourceState 25 (outputArgs a z l) tail := by
  obtain ⟨n,hn⟩ := ax_tail_returns a tail h5 h6 h7
  let b := PA194ModelMPCompare.values (compareInput a) 0 0
  have hv := tail_values a h6 h7
  change b 0 = a 0 ∧ b 1 = 0 ∧ b 2 = cantor (a 1) (a 2) ∧ b 3 = a 3 ∧
    b 4 = a 4 + F fixedFirst ![a 8] ∧ b 5 = 0 ∧ b 6 = 0 ∧ b 7 = 0 ∧
    b 8 = F fixedSecond ![a 8] at hv
  obtain ⟨h0,h1,h2,hb3,hb4,hb5,hb6,hb7,hb8⟩ := hv
  have hfirst : F fixedFirst ![a 8] = z := by rw [hstream,fixedFirst_model,first_cantor]
  have hsecond : F fixedSecond ![a 8] = l := by rw [hstream,fixedSecond_model,second_cantor]
  have hre : regsOfArgs b = regsOfArgs (outputArgs a z l) := by
    funext i
    fin_cases i <;> simp [regsOfArgs,outputArgs,h0,h1,h2,hb3,hb4,hb5,hb6,hb7,hb8,h3,h4,hfirst,hsecond]
  have htarget : sourceState 25 b tail = sourceState 25 (outputArgs a z l) tail := by
    simp only [sourceState,hre]
  change F (iterate PA194AX11HSource.step) ![n,sourceState 3553 a tail] = sourceState 25 b tail at hn
  rw [htarget] at hn
  have hn0 : n ≠ 0 := by
    intro he
    subst n
    rw [iterateZero] at hn
    have hp := congrArg (fun s => F pc ![s]) hn
    rw [statePC,statePC] at hp
    exact (ne_of_gt (modelNumeralStrict 25 3553 (by decide))) hp
  exact ⟨n,lt_of_le_of_ne zero_le (Ne.symm hn0),hn⟩

#print axioms ax_tail_frame
end models
end PA194AX11HAXTailFrame
