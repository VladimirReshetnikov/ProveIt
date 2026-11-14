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
def node61 : Tree := .node node60 node60
def node62 : Tree := .node node61 (.leaf (.continueTo 2))
def node63 : Tree := .node (.leaf (.dec 7)) node62
def node64 : Tree := .node node46 node63
def node65 : Tree := .node node17 node64
def node72 : Tree := .node node32 node19
def node73 : Tree := .node node53 node55
def node74 : Tree := .node node32 node73
def node75 : Tree := .node node74 node65
def node68 : Tree := .node (.leaf (.dec 3)) node50
def node69 : Tree := .node node68 node34
def node70 : Tree := .node node49 node69
def node142 : Tree := .node (.leaf (.dec 3)) node40
def node145 : Tree := .node (.leaf (.dec 1)) (.leaf (.continueTo 1))
def node146 : Tree := .node node6 node145
def node147 : Tree := .node (.leaf (.dec 4)) node18
def node148 : Tree := .node node10 node147
def node149 : Tree := .node node148 node146
def node150 : Tree := .node node146 node149
def g0 : Tree := .node node65 (.leaf (.inc 1))
def g1 : Tree := .node g0 (.leaf (.inc 1))
def g2 : Tree := .node node55 g1
def g3 : Tree := .node node58 g2
def g4 : Tree := .node node72 node58
def g5 : Tree := .node node58 node65
def g6 : Tree := .node node55 g5
def g7 : Tree := .node node70 g5
def g8 : Tree := .node node65 node65
def g9 : Tree := .node g8 g3
def g10 : Tree := .node g7 g9
def g11 : Tree := .node g6 g10
def g12 : Tree := .node (.leaf (.inc 1)) node65
def g13 : Tree := .node node49 g12
def g14 : Tree := .node g13 g2
def g15 : Tree := .node g14 g13
def g16 : Tree := .node g15 g5
def g17 : Tree := .node g11 g16
def g18 : Tree := .node node75 g17
def g19 : Tree := .node node70 g1
def g20 : Tree := .node node58 g19
def g21 : Tree := .node g2 g3
def g22 : Tree := .node g19 node65
def g23 : Tree := .node node55 g0
def g24 : Tree := .node node58 g23
def g25 : Tree := .node g22 g24
def g26 : Tree := .node g21 g25
def g27 : Tree := .node g20 g26
def g28 : Tree := .node g18 g27
def g29 : Tree := .node node65 g28
def g30 : Tree := .node g29 g20
def g31 : Tree := .node node70 g23
def g32 : Tree := .node (.leaf (.inc 1)) g31
def g33 : Tree := .node g9 (.leaf (.inc 1))
def g34 : Tree := .node g32 g33
def g35 : Tree := .node g30 g34
def g36 : Tree := .node node55 g35
def g37 : Tree := .node g15 g31
def g38 : Tree := .node g36 g37
def g39 : Tree := .node (.leaf (.inc 1)) g7
def g40 : Tree := .node g21 g33
def g41 : Tree := .node g39 g40
def g42 : Tree := .node g7 g34
def g43 : Tree := .node g41 g42
def g44 : Tree := .node g38 g43
def g45 : Tree := .node g4 g44
def g46 : Tree := .node g45 g3
def g47 : Tree := .node g3 g46
def g48 : Tree := .node (.leaf (.inc 1)) g25
def g49 : Tree := .node g48 g24
def g50 : Tree := .node g49 g25
def g51 : Tree := .node node70 g31
def g52 : Tree := .node g8 g31
def g53 : Tree := .node g51 g52
def g54 : Tree := .node g50 g53
def g55 : Tree := .node node65 g13
def g56 : Tree := .node g55 node65
def g57 : Tree := .node g51 g56
def g58 : Tree := .node g14 g57
def g59 : Tree := .node g56 g58
def g60 : Tree := .node node70 g59
def g61 : Tree := .node g55 node142
def g62 : Tree := .node g22 g61
def g63 : Tree := .node g60 g62
def g64 : Tree := .node node150 (.leaf (.breakTo 1))
def g65 : Tree := .node g63 g64
def g66 : Tree := .node g54 g65
def g67 : Tree := .node g47 g66
def node161 : Tree := .node (.leaf (.dec 3)) g67
def node162 : Tree := .node node75 node37
def node163 : Tree := .node node6 node55
def node164 : Tree := .node node162 node163
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
