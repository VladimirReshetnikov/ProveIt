import PA194ProgramDrain
import PA194M5Program
import PA194PausedDrain
import PA194SourceControllerBinding
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false
namespace PA194M5FetchAgree
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerStep PA194SourceControllerBinding PA194SourceFetchLoop PA194SchedulerFetchPositive
open PA194PausedDrain PA194ProgramDrain PA194M5Program

theorem rows (i : Fin 23) :
    row program (i.val+25) = (M6.Source.PathTrie.nthSite PA194.SourceTree.trie (i.val+25)).bind
        (M6.FastResolve.resolveTree PA194.SourceTree.trie) := by
  fin_cases i <;> decide +kernel

theorem present (i : Fin 23) : row program (i.val+25) ≠ none ∧ row program (i.val+25) ≠ some .halt := by
  fin_cases i <;> decide +kernel
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
theorem agrees (q : Nat) (hq : 25 ≤ q ∧ q < 48) (a : Fin 11 → M) (tail : M) :
    F (PA194ProgramDrain.step program) ![sourceState q a tail] =
      F PA194SourceControllerCode.step ![sourceState q a tail] := by
  have hc : q < program.length := by rw [programLength]; omega
  have hp : q < 3673 := by omega
  let i : Fin 23 := ⟨q-25, by omega⟩
  have hi : i.val+25 = q := Nat.sub_add_cancel hq.1
  have hr := rows i
  have hn := present i
  rw [hi] at hr hn
  cases h : row program q with
  | none => exact False.elim (hn.1 h)
  | some inst =>
    have hne : inst ≠ .halt := by intro hh; subst inst; exact hn.2 h
    rw [PA194ProgramDrain.rowStep program q hc _ (statePC q a tail) h hne,
      actualInstructionStep q hp _ (statePC q a tail)]
    rw [←hr, h]
#print axioms rows
#print axioms present
#print axioms agrees
end models
end PA194M5FetchAgree
