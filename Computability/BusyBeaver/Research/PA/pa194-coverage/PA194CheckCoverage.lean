import PA194SourceProgram
import PA194CompilerCorrectness
namespace PA194CheckCoverage
open M6.Source M6.Runtime PA194PrimitiveSimulation
open PA194SourceProgram (sites path)
open PA194.SourceTree (trie)
open PA194RuntimeContracts (check haltCheck)

def codeAt (i : Nat) : Option Instruction :=
  (M6.Source.PathTrie.nthSite trie i).bind (M6.FastResolve.resolveTree trie)

def checkInstruction (i : Nat) : Instruction → Bool
  | .inc r next =>
    decide (next.getD 0 < 3673) &&
    check 1024 ⟨none, PA194RuntimeContracts.rootFrame (path i),
      PA194RuntimeContracts.rootFrame (path (next.getD 0)) 0 (.inc (physicalRegister r))⟩
  | .dec r z p =>
    decide (z.getD 0 < 3673 ∧ p.getD 0 < 3673) &&
    (check 1024 ⟨some (physicalRegister r,true), PA194RuntimeContracts.rootFrame (path i),
      PA194RuntimeContracts.rootFrame (path (z.getD 0)) 0 .none⟩ &&
    check 1024 ⟨some (physicalRegister r,false), PA194RuntimeContracts.rootFrame (path i),
      PA194RuntimeContracts.rootFrame (path (p.getD 0)) 1 (.dec (physicalRegister r))⟩)
  | .jump next =>
    decide (next.getD 0 < 3673) &&
    check 1024 ⟨none, PA194RuntimeContracts.rootFrame (path i),
      PA194RuntimeContracts.rootFrame (path (next.getD 0)) 0 .none⟩
  | .halt => haltCheck 1024 none (PA194RuntimeContracts.rootFrame (path i))

def checkAt (i : Nat) : Bool := (codeAt i).any (checkInstruction i)
def blockCheck (base count : Nat) : Bool :=
  (List.range count).all (fun j => checkAt (base+j))

theorem checked_instruction (i : Nat) (code : Instruction)
    (h : checkInstruction i code = true) : Implements path 3673 (path i) code := by
  cases code with
  | inc r next =>
    obtain ⟨hn,hc⟩ := Bool.and_eq_true_iff.mp h
    exact implements_inc path 3673 (path i) r next 0 1024 (of_decide_eq_true hn)
      (PA194SourceProgram.path_short _) hc
  | dec r z p =>
    obtain ⟨hb,hc⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨hz,hp⟩ := of_decide_eq_true hb
    obtain ⟨cz,cp⟩ := Bool.and_eq_true_iff.mp hc
    exact implements_dec path 3673 (path i) r z p 0 1 1024 1024 hz hp
      (PA194SourceProgram.path_short _) (PA194SourceProgram.path_short _) cz cp
  | jump next =>
    obtain ⟨hn,hc⟩ := Bool.and_eq_true_iff.mp h
    exact implements_jump path 3673 (path i) next 0 1024 (of_decide_eq_true hn)
      (PA194SourceProgram.path_short _) hc
  | halt => exact implements_halt path 3673 (path i) 1024 h

theorem checked_at (i : Nat) (h : checkAt i = true) :
    ∃ code, resolveAt sites i = some code ∧ Implements path 3673 (path i) code := by
  unfold checkAt at h
  cases hc : codeAt i with
  | none => simp [hc] at h
  | some code =>
    refine ⟨code,?_,checked_instruction i code ?_⟩
    · rw [PA194SourceProgram.resolve_tree]; exact hc
    · simpa [hc] using h

theorem block_sound {base count i : Nat} (h : blockCheck base count = true)
    (lo : base ≤ i) (hi : i < base+count) : checkAt i = true := by
  have hh := List.all_eq_true.mp h (i-base) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le lo] using hh

#print axioms checked_at
end PA194CheckCoverage
