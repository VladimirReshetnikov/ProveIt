module
public import M6.OriginalProgram
public import M6.Legacy213.SourceCheck
@[expose] public section
namespace M6.Legacy211.Source
open M6.Source M6.Source.PathTrie
def trie : Tree := OriginalProgram.trie
def sites : Array Site := (flatten trie).toArray
def path (i : Nat) : Path := ((nthSite trie i).map (·.path)).getD []
theorem flatten_exact : flatten trie=sites.toList := by simp [sites]
theorem sites_count : sites.size=3947 := by decide +kernel
theorem nthSite_sites (i : Nat) : nthSite trie i=sites[i]? := by
  simpa only [sites,List.getElem?_toArray] using nthSite_eq trie i
theorem resolve_tree (i : Nat) :
    resolveAt sites i=(nthSite trie i).bind (M6.Legacy213.FastResolve.resolveTree trie) := by
  rw [M6.Legacy213.SourceCheck.resolve_eq_tree sites trie flatten_exact,nthSite_sites]
end M6.Legacy211.Source
