import PA194SourceTree
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194SourceProgram
open M6.Source M6.Source.PathTrie M6.FastResolve PA194.SourceTree

def sites : Array Site := (flatten trie).toArray
def path (i : Nat) : Path := ((nthSite trie i).map (·.path)).getD []

theorem flatten_exact : flatten trie = sites.toList := by simp [sites]
theorem sites_count : sites.size = 3673 := by decide +kernel
theorem nthSite_sites (i : Nat) : nthSite trie i = sites[i]? := by
  simpa only [sites,List.getElem?_toArray] using nthSite_eq trie i
theorem resolve_tree (i : Nat) : resolveAt sites i = (nthSite trie i).bind (resolveTree trie) := by
  rw [nthSite_sites]
  unfold resolveAt
  rw [show resolveTree trie = resolve sites from funext (resolveTree_eq trie sites flatten_exact)]
  rfl
theorem all_paths_short : sites.toList.all (fun s => decide (s.path.length ≤ 38)) = true := by decide +kernel
theorem path_short (i : Nat) : (path i).length ≤ 38 := by
  unfold path
  rw [nthSite_sites]
  cases hs : sites[i]? with
  | none => simp [hs]
  | some s =>
    have hm : s ∈ sites.toList := List.mem_of_getElem? (by simpa using hs)
    have hh := List.all_eq_true.mp all_paths_short s hm
    simpa [hs] using hh

#print axioms sites_count
#print axioms resolve_tree
#print axioms path_short
end PA194SourceProgram
