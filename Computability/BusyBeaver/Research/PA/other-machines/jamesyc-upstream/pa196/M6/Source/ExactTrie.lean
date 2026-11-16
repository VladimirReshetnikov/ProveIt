module
public import M6.Source.PathTrie
public import M6.Source.ExactSource
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace M6.Source.PathTrie

def m6node0 : Tree := .node (.leaf (.dec 8)) (.leaf (.breakTo 1))
def m6node1 : Tree := .node (.leaf (.inc 6)) (.leaf (.continueTo 3))
def m6node2 : Tree := .node (.leaf (.inc 8)) m6node1
def m6node3 : Tree := .node (.leaf (.dec 0)) m6node2
def m6node4 : Tree := .node (.leaf (.dec 6)) (.leaf (.continueTo 2))
def m6node5 : Tree := .node (.leaf (.inc 0)) m6node4
def m6node6 : Tree := .node m6node3 m6node5
def m6node7 : Tree := .node m6node0 m6node6
def m6node8 : Tree := .node (.leaf (.dec 6)) (.leaf (.breakTo 1))
def m6node9 : Tree := .node (.leaf (.inc 6)) (.leaf (.continueTo 2))
def m6node10 : Tree := .node (.leaf (.dec 7)) m6node9
def m6node11 : Tree := .node m6node8 m6node10
def m6node12 : Tree := .node m6node11 (.leaf (.continueTo 3))
def m6node13 : Tree := .node (.leaf (.inc 7)) m6node12
def m6node14 : Tree := .node (.leaf (.dec 8)) m6node13
def m6node15 : Tree := .node (.leaf (.inc 8)) (.leaf (.continueTo 2))
def m6node16 : Tree := .node (.leaf (.dec 7)) m6node15
def m6node17 : Tree := .node m6node14 m6node16
def m6node18 : Tree := .node (.leaf (.inc 3)) (.leaf (.continueTo 2))
def m6node19 : Tree := .node (.leaf (.dec 6)) m6node18
def m6node20 : Tree := .node m6node17 m6node19
def m6node21 : Tree := .node m6node7 m6node20
def m6node22 : Tree := .node (.leaf (.dec 1)) m6node9
def m6node23 : Tree := .node (.leaf (.inc 1)) (.leaf (.continueTo 2))
def m6node24 : Tree := .node (.leaf (.dec 2)) m6node23
def m6node25 : Tree := .node (.leaf (.inc 7)) m6node1
def m6node26 : Tree := .node (.leaf (.dec 1)) m6node25
def m6node27 : Tree := .node (.leaf (.dec 6)) m6node23
def m6node28 : Tree := .node (.leaf (.inc 7)) m6node27
def m6node29 : Tree := .node m6node28 (.leaf (.continueTo 3))
def m6node30 : Tree := .node (.leaf (.dec 6)) m6node29
def m6node31 : Tree := .node m6node26 m6node30
def m6node32 : Tree := .node (.leaf (.inc 2)) (.leaf (.continueTo 2))
def m6node33 : Tree := .node (.leaf (.dec 7)) m6node32
def m6node34 : Tree := .node m6node31 m6node33
def m6node35 : Tree := .node m6node24 m6node34
def m6node36 : Tree := .node m6node22 m6node35
def m6node37 : Tree := .node (.leaf (.inc 1)) m6node1
def m6node38 : Tree := .node (.leaf (.dec 4)) m6node37
def m6node39 : Tree := .node (.leaf (.inc 4)) (.leaf (.continueTo 2))
def m6node40 : Tree := .node (.leaf (.dec 6)) m6node39
def m6node41 : Tree := .node m6node38 m6node40
def m6node42 : Tree := .node m6node36 m6node41
def m6node43 : Tree := .node (.leaf (.dec 5)) m6node37
def m6node44 : Tree := .node (.leaf (.inc 5)) (.leaf (.continueTo 2))
def m6node45 : Tree := .node (.leaf (.dec 6)) m6node44
def m6node46 : Tree := .node m6node43 m6node45
def m6node47 : Tree := .node m6node36 m6node46
def m6node48 : Tree := .node m6node42 m6node47
def m6node49 : Tree := .node (.leaf (.dec 2)) m6node13
def m6node50 : Tree := .node m6node49 m6node33
def m6node51 : Tree := .node (.leaf (.inc 1)) (.leaf (.inc 1))
def m6node52 : Tree := .node m6node51 m6node51
def m6node53 : Tree := .node m6node52 (.leaf (.continueTo 2))
def m6node54 : Tree := .node (.leaf (.dec 7)) m6node53
def m6node55 : Tree := .node m6node31 m6node54
def m6node56 : Tree := .node m6node50 m6node55
def m6node57 : Tree := .node m6node56 m6node51
def m6node58 : Tree := .node (.leaf (.dec 3)) m6node37
def m6node59 : Tree := .node m6node58 m6node19
def m6node60 : Tree := .node m6node36 m6node59
def m6node61 : Tree := .node m6node60 m6node42
def m6node62 : Tree := .node m6node17 m6node45
def m6node63 : Tree := .node m6node40 m6node42
def m6node64 : Tree := .node m6node17 m6node63
def m6node65 : Tree := .node m6node64 m6node56
def m6node66 : Tree := .node m6node56 m6node65
def m6node67 : Tree := .node m6node62 m6node66
def m6node68 : Tree := .node m6node42 m6node60
def m6node69 : Tree := .node m6node47 m6node60
def m6node70 : Tree := .node m6node56 m6node69
def m6node71 : Tree := .node m6node56 m6node56
def m6node72 : Tree := .node m6node70 m6node71
def m6node73 : Tree := .node m6node68 m6node72
def m6node74 : Tree := .node m6node67 m6node73
def m6node75 : Tree := .node m6node56 (.leaf (.inc 1))
def m6node76 : Tree := .node m6node61 m6node75
def m6node77 : Tree := .node m6node60 m6node47
def m6node78 : Tree := .node m6node77 m6node75
def m6node79 : Tree := .node m6node51 m6node78
def m6node80 : Tree := .node m6node76 m6node79
def m6node81 : Tree := .node m6node56 m6node80
def m6node82 : Tree := .node m6node74 m6node81
def m6node83 : Tree := .node m6node61 m6node82
def m6node84 : Tree := .node m6node48 m6node75
def m6node85 : Tree := .node m6node48 m6node57
def m6node86 : Tree := .node m6node85 (.leaf (.inc 1))
def m6node87 : Tree := .node m6node84 m6node86
def m6node88 : Tree := .node m6node51 m6node87
def m6node89 : Tree := .node m6node71 m6node42
def m6node90 : Tree := .node m6node36 (.leaf (.inc 1))
def m6node91 : Tree := .node m6node56 m6node57
def m6node92 : Tree := .node m6node90 m6node56
def m6node93 : Tree := .node m6node91 m6node92
def m6node94 : Tree := .node m6node90 m6node93
def m6node95 : Tree := .node m6node94 m6node47
def m6node96 : Tree := .node m6node85 m6node95
def m6node97 : Tree := .node m6node89 m6node96
def m6node98 : Tree := .node m6node57 m6node97
def m6node99 : Tree := .node m6node88 m6node98
def m6node100 : Tree := .node m6node89 m6node69
def m6node101 : Tree := .node m6node84 m6node100
def m6node102 : Tree := .node m6node81 m6node101
def m6node103 : Tree := .node m6node57 m6node56
def m6node104 : Tree := .node m6node102 m6node103
def m6node105 : Tree := .node m6node99 m6node104
def m6node106 : Tree := .node m6node83 m6node105
def m6node107 : Tree := .node m6node57 m6node106
def m6node108 : Tree := .node m6node68 m6node57
def m6node109 : Tree := .node m6node103 m6node86
def m6node110 : Tree := .node m6node108 m6node109
def m6node111 : Tree := .node m6node47 m6node110
def m6node112 : Tree := .node m6node76 m6node78
def m6node113 : Tree := .node m6node111 m6node112
def m6node114 : Tree := .node m6node113 m6node100
def m6node115 : Tree := .node m6node51 m6node114
def m6node116 : Tree := .node m6node89 m6node86
def m6node117 : Tree := .node m6node108 m6node116
def m6node118 : Tree := .node m6node85 m6node117
def m6node119 : Tree := .node m6node91 m6node118
def m6node120 : Tree := .node m6node115 m6node119
def m6node121 : Tree := .node m6node120 m6node94
def m6node122 : Tree := .node m6node84 m6node103
def m6node123 : Tree := .node m6node60 m6node122
def m6node124 : Tree := .node m6node84 m6node60
def m6node125 : Tree := .node m6node77 m6node124
def m6node126 : Tree := .node m6node71 m6node78
def m6node127 : Tree := .node m6node78 m6node126
def m6node128 : Tree := .node m6node125 m6node127
def m6node129 : Tree := .node m6node123 m6node128
def m6node130 : Tree := .node m6node56 m6node92
def m6node131 : Tree := .node m6node130 m6node130
def m6node132 : Tree := .node m6node60 m6node131
def m6node133 : Tree := .node m6node57 m6node60
def m6node134 : Tree := .node m6node78 m6node130
def m6node135 : Tree := .node m6node133 m6node134
def m6node136 : Tree := .node m6node132 m6node135
def m6node137 : Tree := .node (.leaf (.dec 3)) m6node25
def m6node138 : Tree := .node m6node130 m6node137
def m6node139 : Tree := .node m6node91 m6node138
def m6node140 : Tree := .node m6node4 (.leaf (.breakTo 1))
def m6node141 : Tree := .node (.leaf (.dec 5)) m6node140
def m6node142 : Tree := .node m6node141 (.leaf (.dec 6))
def m6node143 : Tree := .node (.leaf (.dec 5)) (.leaf (.continueTo 1))
def m6node144 : Tree := .node m6node143 m6node140
def m6node145 : Tree := .node m6node142 m6node144
def m6node146 : Tree := .node (.leaf (.dec 1)) (.leaf (.continueTo 1))
def m6node147 : Tree := .node m6node145 m6node146
def m6node148 : Tree := .node (.leaf (.dec 4)) m6node44
def m6node149 : Tree := .node m6node10 m6node148
def m6node150 : Tree := .node m6node149 m6node147
def m6node151 : Tree := .node m6node147 m6node150
def m6node152 : Tree := .node m6node139 m6node151
def m6node153 : Tree := .node m6node136 m6node152
def m6node154 : Tree := .node m6node129 m6node153
def m6node155 : Tree := .node m6node84 m6node154
def m6node156 : Tree := .node m6node121 m6node155
def m6node157 : Tree := .node m6node107 m6node156
def m6node158 : Tree := .node m6node48 m6node157
def m6node159 : Tree := .node m6node158 (.leaf (.breakTo 1))
def m6node160 : Tree := .node (.leaf (.dec 3)) m6node159
def m6node161 : Tree := .node m6node65 m6node22
def m6node162 : Tree := .node m6node145 m6node42
def m6node163 : Tree := .node m6node161 m6node162
def m6node164 : Tree := .node m6node160 m6node163
def m6node165 : Tree := .node m6node164 (.leaf (.continueTo 3))
def m6node166 : Tree := .node (.leaf (.dec 3)) m6node165
def m6node167 : Tree := .node m6node145 (.leaf (.halt))
def m6node168 : Tree := .node m6node50 m6node45
def m6node169 : Tree := .node m6node167 m6node168
def m6node170 : Tree := .node (.leaf (.inc 6)) m6node169
def m6node171 : Tree := .node m6node46 m6node170
def m6node172 : Tree := .node m6node22 m6node171
def m6node173 : Tree := .node m6node166 m6node172
def m6node174 : Tree := .node m6node21 m6node173
def exactTrie : Tree := m6node174

/-- Full literal transcription check, not a trusted generator assertion. -/
theorem exact_flatten : flatten exactTrie = exactSites.toList := by rfl

theorem exact_lookup (p : Path) : lookup exactTrie p = locate exactSites p := by
  rw [lookup_eq,exact_flatten]
  rfl
#print axioms exact_flatten
#print axioms exact_lookup
end M6.Source.PathTrie

