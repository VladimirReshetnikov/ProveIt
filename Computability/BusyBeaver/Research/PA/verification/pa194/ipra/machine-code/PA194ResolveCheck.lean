import PA194SourceControllerCode
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194ResolveCheck
open M6.Source M6.Source.PathTrie PA194.SourceTree

def codeAt (i : Nat) : Option Instruction :=
  (nthSite trie i).bind (M6.FastResolve.resolveTree trie)
def check (base count : Nat) : Bool :=
  (List.range count).all (fun j => (codeAt (base+j)).isSome)

theorem block_sound {base count i : Nat} (h : check base count = true)
    (lo : base ≤ i) (hi : i < base+count) :
    ∃ inst, resolveAt PA194SourceProgram.sites i = some inst := by
  have hh := List.all_eq_true.mp h (i-base) (List.mem_range.mpr (by omega))
  have hc : (codeAt i).isSome = true := by
    simpa only [Nat.add_sub_of_le lo] using hh
  cases he : codeAt i with
  | none => simp [he] at hc
  | some inst =>
    refine ⟨inst,?_⟩
    rw [PA194SourceProgram.resolve_tree]
    exact he
#print axioms block_sound
end PA194ResolveCheck
