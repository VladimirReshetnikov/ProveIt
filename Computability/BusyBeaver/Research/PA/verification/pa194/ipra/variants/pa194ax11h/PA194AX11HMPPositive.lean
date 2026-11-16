import PA194AX11HMPCommand
import PA194StateOne
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194AX11HMPPositive
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion PRASubAddition TableDispatch
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194SourceFetchLoop
open PA194IteratedSimulation PA194ControllerRunAdd PA194SourcePCBound PA194StateOne
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

theorem fromFetch (a b : Fin 11 → M) (tail : M)
    (h : PA194PausedReach.Reaches PA194AX11HSource.step (sourceState 25 a tail) (sourceState 48 b tail))
    (opcode : b 3 = 1) (hx : b 6 = 0) (hy : b 7 = 0) :
    ∃ n : M, 0 < n ∧ F (iterate PA194AX11HSource.step) ![n,sourceState 25 a tail] =
      sourceState 25 (PA194AX11HMPSource.output (Function.update b 3 0)) tail := by
  obtain ⟨n,hn⟩ := h
  have hn0 : n ≠ 0 := by
    intro he
    subst n
    rw [iterateZero] at hn
    have hp := congrArg (fun s => F pc ![s]) hn
    rw [statePC,statePC] at hp
    exact (ne_of_lt (modelNumeralStrict 25 48 (by decide))) hp
  obtain ⟨m,hm⟩ := PA194AX11HMPCommand.decoded b tail opcode hx hy
  refine ⟨n+m,lt_of_lt_of_le (lt_of_le_of_ne zero_le (Ne.symm hn0)) (le_add_of_nonneg_right zero_le),?_⟩
  rw [iterateAdd,hn,hm]
#print axioms fromFetch
end models
end PA194AX11HMPPositive
