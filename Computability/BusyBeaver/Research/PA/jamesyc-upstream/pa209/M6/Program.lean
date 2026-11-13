module
public import M6.TreeSite
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 64000000
namespace M6.Program
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
def node51 : Tree := .node (.leaf (.dec 4)) node50
def node52 : Tree := .node (.leaf (.inc 4)) (.leaf (.continueTo 2))
def node53 : Tree := .node (.leaf (.dec 6)) node52
def node54 : Tree := .node node51 node53
def node55 : Tree := .node node49 node54
def node56 : Tree := .node (.leaf (.dec 5)) node50
def node57 : Tree := .node node56 node19
def node58 : Tree := .node node49 node57
def node59 : Tree := .node node55 node58
def node60 : Tree := .node (.leaf (.inc 1)) (.leaf (.inc 1))
def node61 : Tree := .node node60 node60
def node62 : Tree := .node node61 (.leaf (.continueTo 2))
def node63 : Tree := .node (.leaf (.dec 7)) node62
def node64 : Tree := .node node46 node63
def node65 : Tree := .node node17 node64
def node66 : Tree := .node node65 node60
def node67 : Tree := .node node59 node66
def node68 : Tree := .node (.leaf (.dec 3)) node50
def node69 : Tree := .node node68 node34
def node70 : Tree := .node node49 node69
def node71 : Tree := .node node70 node55
def node72 : Tree := .node node32 node19
def node73 : Tree := .node node53 node55
def node74 : Tree := .node node32 node73
def node75 : Tree := .node node74 node65
def node76 : Tree := .node node65 node75
def node77 : Tree := .node node72 node76
def node78 : Tree := .node node55 node70
def node79 : Tree := .node node58 node70
def node80 : Tree := .node node65 node79
def node81 : Tree := .node node65 node65
def node82 : Tree := .node node65 (.leaf (.inc 1))
def node83 : Tree := .node node71 node82
def node84 : Tree := .node node70 node58
def node85 : Tree := .node node84 node82
def node86 : Tree := .node node60 node85
def node87 : Tree := .node node83 node86
def node88 : Tree := .node node65 node87
def node89 : Tree := .node node81 node88
def node90 : Tree := .node node80 node89
def node91 : Tree := .node node78 node90
def node92 : Tree := .node node77 node91
def node93 : Tree := .node node71 node92
def node94 : Tree := .node node59 node82
def node95 : Tree := .node node67 (.leaf (.inc 1))
def node96 : Tree := .node node94 node95
def node97 : Tree := .node node60 node96
def node98 : Tree := .node node81 node55
def node99 : Tree := .node node49 (.leaf (.inc 1))
def node100 : Tree := .node node65 node66
def node101 : Tree := .node node99 node65
def node102 : Tree := .node node100 node101
def node103 : Tree := .node node99 node102
def node104 : Tree := .node node103 node58
def node105 : Tree := .node node67 node104
def node106 : Tree := .node node98 node105
def node107 : Tree := .node node66 node106
def node108 : Tree := .node node97 node107
def node109 : Tree := .node node98 node79
def node110 : Tree := .node node94 node109
def node111 : Tree := .node node88 node110
def node112 : Tree := .node node66 node65
def node113 : Tree := .node node111 node112
def node114 : Tree := .node node108 node113
def node115 : Tree := .node node78 node66
def node116 : Tree := .node node112 node95
def node117 : Tree := .node node115 node116
def node118 : Tree := .node node58 node117
def node119 : Tree := .node node83 node85
def node120 : Tree := .node node118 node119
def node121 : Tree := .node node120 node109
def node122 : Tree := .node node60 node121
def node123 : Tree := .node node98 node95
def node124 : Tree := .node node115 node123
def node125 : Tree := .node node67 node124
def node126 : Tree := .node node100 node125
def node127 : Tree := .node node126 node103
def node128 : Tree := .node node122 node127
def node129 : Tree := .node node94 node112
def node130 : Tree := .node node70 node129
def node131 : Tree := .node node84 node94
def node132 : Tree := .node node70 node85
def node133 : Tree := .node node131 node132
def node134 : Tree := .node node130 node133
def node135 : Tree := .node node81 node85
def node136 : Tree := .node node65 node101
def node137 : Tree := .node node136 node136
def node138 : Tree := .node node70 node137
def node139 : Tree := .node node66 node132
def node140 : Tree := .node node139 node136
def node141 : Tree := .node node138 node140
def node142 : Tree := .node (.leaf (.dec 3)) node40
def node143 : Tree := .node node136 node142
def node144 : Tree := .node node100 node143
def node145 : Tree := .node (.leaf (.dec 1)) (.leaf (.continueTo 1))
def node146 : Tree := .node node6 node145
def node147 : Tree := .node (.leaf (.dec 4)) node18
def node148 : Tree := .node node10 node147
def node149 : Tree := .node node148 node146
def node150 : Tree := .node node146 node149
def node151 : Tree := .node node144 node150
def node152 : Tree := .node node141 node151
def node153 : Tree := .node node135 node152
def node154 : Tree := .node node134 node153
def node155 : Tree := .node node94 node154
def node156 : Tree := .node node128 node155
def node157 : Tree := .node node156 (.leaf (.breakTo 1))
def node158 : Tree := .node node114 node157
def node159 : Tree := .node node93 node158
def node160 : Tree := .node node67 node159
def node161 : Tree := .node (.leaf (.dec 3)) node160
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
theorem sites_count : sites.size = 3948 := by decide +kernel
theorem nthSite_sites (i : Nat) : nthSite trie i = sites[i]? := by
  simpa only [sites,List.getElem?_toArray] using nthSite_eq trie i
theorem resolve_tree (i : Nat) : resolveAt sites i = (nthSite trie i).bind (FastResolve.resolveTree trie) := by
  rw [nthSite_sites]
  unfold resolveAt
  rw [show FastResolve.resolveTree trie = resolve sites from funext (FastResolve.resolveTree_eq trie sites flatten_exact)]
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
end M6.Program
