module
public import M6.Program
public import M6.CompilerCorrectness
@[expose] public section
namespace M6.CheckCoverage
open M6.Source M6.Runtime M6.PrimitiveSimulation
open M6.Program (sites path trie)
open M6.RuntimeContracts (check haltCheck)

def codeAt (i : Nat) : Option Instruction :=
  (Source.PathTrie.nthSite trie i).bind (FastResolve.resolveTree trie)

def checkInstruction (i : Nat) : Instruction → Bool
  | .inc r next =>
    decide (next.getD 0 < 3948) &&
    check 1024 ⟨none, RuntimeContracts.rootFrame (path i),
      RuntimeContracts.rootFrame (path (next.getD 0)) 0 (.inc (physicalRegister r))⟩
  | .dec r z p =>
    decide (z.getD 0 < 3948 ∧ p.getD 0 < 3948) &&
    (check 1024 ⟨some (physicalRegister r,true), RuntimeContracts.rootFrame (path i),
      RuntimeContracts.rootFrame (path (z.getD 0)) 0 .none⟩ &&
    check 1024 ⟨some (physicalRegister r,false), RuntimeContracts.rootFrame (path i),
      RuntimeContracts.rootFrame (path (p.getD 0)) 1 (.dec (physicalRegister r))⟩)
  | .jump next =>
    decide (next.getD 0 < 3948) &&
    check 1024 ⟨none, RuntimeContracts.rootFrame (path i),
      RuntimeContracts.rootFrame (path (next.getD 0)) 0 .none⟩
  | .halt => haltCheck 1024 none (RuntimeContracts.rootFrame (path i))

def checkAt (i : Nat) : Bool := (codeAt i).any (checkInstruction i)
def blockCheck (base count : Nat) : Bool :=
  (List.range count).all (fun j => checkAt (base+j))

theorem checked_instruction (i : Nat) (code : Instruction)
    (h : checkInstruction i code = true) : Implements path 3948 (path i) code := by
  cases code with
  | inc r next =>
    obtain ⟨hn,hc⟩ := Bool.and_eq_true_iff.mp h
    exact implements_inc path 3948 (path i) r next 0 1024 (of_decide_eq_true hn)
      (Program.path_short _) hc
  | dec r z p =>
    obtain ⟨hb,hc⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨hz,hp⟩ := of_decide_eq_true hb
    obtain ⟨cz,cp⟩ := Bool.and_eq_true_iff.mp hc
    exact implements_dec path 3948 (path i) r z p 0 1 1024 1024 hz hp
      (Program.path_short _) (Program.path_short _) cz cp
  | jump next =>
    obtain ⟨hn,hc⟩ := Bool.and_eq_true_iff.mp h
    exact implements_jump path 3948 (path i) next 0 1024 (of_decide_eq_true hn)
      (Program.path_short _) hc
  | halt => exact implements_halt path 3948 (path i) 1024 h

theorem checked_at (i : Nat) (h : checkAt i = true) :
    ∃ code, resolveAt sites i = some code ∧ Implements path 3948 (path i) code := by
  unfold checkAt at h
  cases hc : codeAt i with
  | none => simp [hc] at h
  | some code =>
    refine ⟨code,?_,checked_instruction i code ?_⟩
    · rw [Program.resolve_tree]; exact hc
    · simpa [hc] using h

theorem block_sound {base count i : Nat} (h : blockCheck base count = true)
    (lo : base ≤ i) (hi : i < base+count) : checkAt i = true := by
  have hh := List.all_eq_true.mp h (i-base) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le lo] using hh

#print axioms checked_at
end M6.CheckCoverage
