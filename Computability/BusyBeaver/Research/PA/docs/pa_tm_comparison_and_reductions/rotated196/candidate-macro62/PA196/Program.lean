module
public import M6.TreeSite
/-! The 159-node DAG stored in the supplied PA196 machine metadata. -/
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA196.Program
open M6.Source M6.Source.PathTrie
def node0 : Tree := .node (.leaf (.dec 6)) (.leaf (.continueTo 2))
def node1 : Tree := .node node0 (.leaf (.breakTo 1))
def node2 : Tree := .node (.leaf (.dec 5)) node1
def node3 : Tree := .node node2 (.leaf (.dec 6))
def node4 : Tree := .node (.leaf (.dec 5)) (.leaf (.continueTo 1))
def node5 : Tree := .node node4 node1
def node6 : Tree := .node node3 node5
def node7 : Tree := .node node6 (.leaf (.halt))
def node8 : Tree := .node (.leaf (.dec 6)) (.leaf (.breakTo 1))
def node9 : Tree := .node (.leaf (.inc 6)) (.leaf (.continueTo 2))
def node10 : Tree := .node (.leaf (.dec 7)) node9
def node11 : Tree := .node node8 node10
def node12 : Tree := .node node11 (.leaf (.continueTo 3))
def node13 : Tree := .node (.leaf (.inc 7)) node12
def node14 : Tree := .node (.leaf (.dec 2)) node13
def node15 : Tree := .node (.leaf (.inc 2)) (.leaf (.continueTo 2))
def node16 : Tree := .node (.leaf (.dec 7)) node15
def node17 : Tree := .node node14 node16
def node18 : Tree := .node (.leaf (.inc 5)) (.leaf (.continueTo 2))
def node19 : Tree := .node (.leaf (.dec 6)) node18
def node20 : Tree := .node node17 node19
def node21 : Tree := .node node7 node20
def node22 : Tree := .node (.leaf (.dec 8)) (.leaf (.breakTo 1))
def node23 : Tree := .node (.leaf (.inc 6)) (.leaf (.continueTo 3))
def node24 : Tree := .node (.leaf (.inc 8)) node23
def node25 : Tree := .node (.leaf (.dec 0)) node24
def node26 : Tree := .node (.leaf (.inc 0)) node0
def node27 : Tree := .node node25 node26
def node28 : Tree := .node node22 node27
def node29 : Tree := .node (.leaf (.dec 8)) node13
def node30 : Tree := .node (.leaf (.inc 8)) (.leaf (.continueTo 2))
def node31 : Tree := .node (.leaf (.dec 7)) node30
def node32 : Tree := .node node29 node31
def node33 : Tree := .node (.leaf (.inc 3)) (.leaf (.continueTo 2))
def node34 : Tree := .node (.leaf (.dec 6)) node33
def node35 : Tree := .node node32 node34
def node36 : Tree := .node node28 node35
def node37 : Tree := .node (.leaf (.dec 1)) node9
def node38 : Tree := .node (.leaf (.inc 1)) (.leaf (.continueTo 2))
def node39 : Tree := .node (.leaf (.dec 2)) node38
def node40 : Tree := .node (.leaf (.inc 7)) node23
def node41 : Tree := .node (.leaf (.dec 1)) node40
def node42 : Tree := .node (.leaf (.dec 6)) node38
def node43 : Tree := .node (.leaf (.inc 7)) node42
def node44 : Tree := .node node43 (.leaf (.continueTo 3))
def node45 : Tree := .node (.leaf (.dec 6)) node44
def node46 : Tree := .node node41 node45
def node47 : Tree := .node node46 node16
def node48 : Tree := .node node39 node47
def node49 : Tree := .node node37 node48
def node50 : Tree := .node (.leaf (.inc 1)) node23
def node56 : Tree := .node (.leaf (.dec 5)) node50
def node57 : Tree := .node node56 node19
def node58 : Tree := .node node49 node57
def node51 : Tree := .node (.leaf (.dec 4)) node50
def node52 : Tree := .node (.leaf (.inc 4)) (.leaf (.continueTo 2))
def node53 : Tree := .node (.leaf (.dec 6)) node52
def node54 : Tree := .node node51 node53
def node55 : Tree := .node node49 node54
def node60 : Tree := .node (.leaf (.inc 1)) (.leaf (.inc 1))
def node61 : Tree := .node node60 (.leaf (.continueTo 3))
def node62 : Tree := .node node60 node61
def node63 : Tree := .node (.leaf (.dec 7)) node62
def node64 : Tree := .node node46 node63
def node65 : Tree := .node node17 node64
def x0 : Tree := .node node65 (.leaf (.inc 1))
def x1 : Tree := .node x0 (.leaf (.inc 1))
def x2 : Tree := .node node55 x1
def x3 : Tree := .node node58 x2
def node72 : Tree := .node node32 node19
def node73 : Tree := .node node53 node55
def node74 : Tree := .node node32 node73
def node75 : Tree := .node node74 node65
def x4 : Tree := .node node58 node65
def x5 : Tree := .node node55 x4
def node68 : Tree := .node (.leaf (.dec 3)) node50
def node69 : Tree := .node node68 node34
def node70 : Tree := .node node49 node69
def x6 : Tree := .node node70 x4
def x7 : Tree := .node node65 node65
def x8 : Tree := .node x7 x3
def x9 : Tree := .node x6 x8
def x10 : Tree := .node x5 x9
def x11 : Tree := .node (.leaf (.inc 1)) node65
def x12 : Tree := .node node49 x11
def x13 : Tree := .node x12 x2
def x14 : Tree := .node x13 x12
def x15 : Tree := .node x14 x4
def x16 : Tree := .node x10 x15
def x17 : Tree := .node node75 x16
def x18 : Tree := .node node70 x1
def x19 : Tree := .node node58 x18
def x20 : Tree := .node x2 x3
def x21 : Tree := .node x18 node65
def x22 : Tree := .node node55 x0
def x23 : Tree := .node node58 x22
def x24 : Tree := .node x21 x23
def x25 : Tree := .node x20 x24
def x26 : Tree := .node x19 x25
def x27 : Tree := .node x17 x26
def x28 : Tree := .node node65 x27
def x29 : Tree := .node x28 x19
def x30 : Tree := .node node70 x22
def x31 : Tree := .node (.leaf (.inc 1)) x30
def x32 : Tree := .node x8 (.leaf (.inc 1))
def x33 : Tree := .node x31 x32
def x34 : Tree := .node x6 x33
def x35 : Tree := .node x33 x34
def x36 : Tree := .node x29 x35
def x37 : Tree := .node node55 x36
def x38 : Tree := .node x14 x30
def x39 : Tree := .node x37 x38
def x40 : Tree := .node node58 x39
def x41 : Tree := .node (.leaf (.inc 1)) x6
def x42 : Tree := .node x20 x32
def x43 : Tree := .node x41 x42
def x44 : Tree := .node x43 x3
def x45 : Tree := .node (.leaf (.inc 1)) x24
def x46 : Tree := .node x45 x23
def x47 : Tree := .node x44 x46
def x48 : Tree := .node x47 x24
def x49 : Tree := .node x40 x48
def x50 : Tree := .node node70 x30
def x51 : Tree := .node x7 x30
def x52 : Tree := .node x50 x51
def x53 : Tree := .node x49 x52
def x54 : Tree := .node node72 x53
def x55 : Tree := .node node65 x12
def x56 : Tree := .node x55 node65
def x57 : Tree := .node x50 x56
def x58 : Tree := .node x13 x57
def x59 : Tree := .node x56 x58
def x60 : Tree := .node node70 x59
def node142 : Tree := .node (.leaf (.dec 3)) node40
def x61 : Tree := .node x55 node142
def x62 : Tree := .node x21 x61
def x63 : Tree := .node x60 x62
def x64 : Tree := .node x54 x63
def node145 : Tree := .node (.leaf (.dec 1)) (.leaf (.continueTo 1))
def node146 : Tree := .node node6 node145
def node147 : Tree := .node (.leaf (.dec 4)) node18
def node148 : Tree := .node node10 node147
def node149 : Tree := .node node148 node146
def node150 : Tree := .node node146 node149
def x65 : Tree := .node node150 (.leaf (.breakTo 1))
def x66 : Tree := .node x64 x65
def x67 : Tree := .node x3 x66
def node161 : Tree := .node (.leaf (.dec 3)) x67
def node163 : Tree := .node node6 node55
def node162 : Tree := .node node37 node163
def node164 : Tree := .node node75 node162
def node165 : Tree := .node node161 node164
def node166 : Tree := .node node165 (.leaf (.continueTo 3))
def node167 : Tree := .node (.leaf (.dec 3)) node166
def node168 : Tree := .node node37 node57
def node169 : Tree := .node node167 node168
def node170 : Tree := .node node36 node169
def node171 : Tree := .node node170 node23
def node172 : Tree := .node node21 node171
def trie : Tree := node172
def sites : Array Site := (flatten trie).toArray
def path (i : Nat) : Path := ((nthSite trie i).map (·.path)).getD []
theorem flatten_exact : flatten trie = sites.toList := by simp [sites]
theorem sites_count : sites.size = 3812 := by decide +kernel
theorem nthSite_sites (i : Nat) : nthSite trie i = sites[i]? := by
  simpa only [sites,List.getElem?_toArray] using nthSite_eq trie i
theorem resolve_tree (i : Nat) : resolveAt sites i = (nthSite trie i).bind (M6.FastResolve.resolveTree trie) := by
  rw [nthSite_sites]
  unfold resolveAt
  rw [show M6.FastResolve.resolveTree trie = resolve sites from funext (M6.FastResolve.resolveTree_eq trie sites flatten_exact)]
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
theorem path_eq (i : Nat) : path i = ((sites[i]?).map (·.path)).getD [] := by rw [path,nthSite_sites]
#print axioms sites_count
#print axioms path_short
end PA196.Program
