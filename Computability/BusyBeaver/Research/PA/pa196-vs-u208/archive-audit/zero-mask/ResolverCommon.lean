import SegmentBase
import PA196.Program
/-! The optimized upstream resolver and the out-of-range table equality. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PA196ZeroMask
open M6.Source M6.Source.PathTrie

def sourceFast (i : Nat) : Option Instruction :=
  (nthSite PA196.Program.trie i).bind (M6.FastResolve.resolveTree PA196.Program.trie)

theorem resolverOutside (i : Nat) (h : 3812 ≤ i) :
    resolveAt PA196.Program.sites i = segmentedLookup i := by
  have hn : PA196.Program.sites[i]? = none := by
    apply Array.getElem?_eq_none
    simpa only [PA196.Program.sites_count] using h
  simp [resolveAt, hn, segmentedLookup, Nat.not_lt.mpr h]
#print axioms resolverOutside
end PA196ZeroMask
