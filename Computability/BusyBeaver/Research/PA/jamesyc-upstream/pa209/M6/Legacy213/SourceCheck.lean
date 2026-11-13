module
public import M6.Legacy213.SourceProgram
@[expose] public section
namespace M6.Legacy213.SourceCheck
open M6.Source M6.Source.PathTrie M6.Legacy213.FastResolve M6.Legacy213.SourceProgram

def atCheck (i : Nat) : Bool :=
  (((sites[i]?).bind (resolveTree trie)) == codes[i]?) &&
  (((exactSites[i]?).bind (resolveTree exactTrie)) == codes[i]?) &&
  decide ((path i).length ≤ 64)

def rangeCheck (base count : Nat) : Bool :=
  (List.range count).all fun j => atCheck (base + j)

theorem range_sound {base count : Nat} (h : rangeCheck base count = true)
    (i : Nat) (hi : base ≤ i) (hi' : i < base + count) : atCheck i = true := by
  have hmem : i-base ∈ List.range count := List.mem_range.mpr (by omega)
  have hh := List.all_eq_true.mp h (i-base) hmem
  simpa only [Nat.add_sub_of_le hi] using hh

theorem resolve_eq_tree (ss : Array Site) (t : Tree) (ht : flatten t = ss.toList) (i : Nat) :
    resolveAt ss i = ((ss[i]?).bind (resolveTree t)) := by
  have hf : resolveTree t = resolve ss := funext (resolveTree_eq t ss ht)
  simp only [hf,resolveAt]
  rfl
end M6.Legacy213.SourceCheck
