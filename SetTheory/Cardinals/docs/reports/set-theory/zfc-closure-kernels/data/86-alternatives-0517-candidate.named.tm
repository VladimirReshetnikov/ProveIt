#! start 0.boot.A
# Based on the NQL register machine:
# <https://github.com/sorear/metamath-turing-machines>
#
# States that begin with a digit are the states for the framework of the
# register machine implemented in a turing machine. States that don't begin
# with a digit are the decision tree states from the subroutines and main().
#
# 0. boot
#
0.boot.A 0 1 R 0.boot.B
0.boot.A 1 0 L 0.boot.C
0.boot.B 0 0 R 0.boot.C
0.boot.B 1 0 R 0.boot.B
0.boot.C 0 1 L 0.boot.D
0.boot.C 1 0 R 0.boot.E
0.boot.D 0 0 L 0.boot.E
0.boot.D 1 0 L 6.continue.4
0.boot.E 0 1 L 0.boot.A
0.boot.E 1 0 L 0.boot.B
#
# At the end of boot the tape looks like:
# 100 1000^4 <3.continue.4 01^132 011 01^68
#
# 1. 2. Low-level register operations:
#
# SEL - Shift which register is selected:
#
# 1 [IP] 1.sel> [ZEROS] [REG BLOCK 1] 0 [REG] 00 [REG BLOCK 2]
# ->
# 5.root> 1 [break.0(IP)] [ZEROS] [REG BLOCK 1] 00 [REG] 0 [REG BLOCK 2]
#
# where IP          is the run length limited in 0s instruction pointer,
#       ZEROS       is a run of at least 3 0s,
#       REG BLOCK 1 starts and ends with 1s and has no run of more than one 0,
#       REG BLOCK 2 can have registers or can be empty.
#
# If 00 does not appear in the register file it is conceptually after the last register.
#
# 00 selects the register that appears after it.
#
# INC - Increment selected register.
#
# 1 [IP] 1.inc> [ZEROS] [REG BLOCK 1] 00 [REG] 0 [REG BLOCK 2]
# ->
# 5.root> 1 [break.0(IP)] [ZEROS] [REG BLOCK 1] 0 [inc(REG)] 0 [REG BLOCK 2]
#
# where IP          is the run length limited in 0s instruction pointer,
#       ZEROS       is a run of at least 3 0s,
#       REG BLOCK 1 starts and ends with 1s and has no run of more than one 0,
#       REG BLOCK 2 can have registers or can be empty.
#
# DECNZ - Decrement selected register if not zero.
#          Break an extra layer if it was 0.
#
# 1 [IP] 1.decnz> [ZEROS] [REG BLOCK 1] 00 [REG] 0 [REG BLOCK 2]
# ->
# 5.root> 1 [break.0(IP)] [ZEROS] 0 [REG BLOCK 1] 0 [dec(REG)] 0 [REG BLOCK 2] 0
#
# where IP          is the run length limited in 0s instruction pointer,
#       ZEROS       is a run of at least 2 0s,
#       REG BLOCK 1 starts and ends with 1s and has no runs of more than one 0,
#       REG         is a run of at least two 1s,
#       REG BLOCK 2 is either empty or starts and ends with 1s and has no run of
#                   more than one 0.
#
# or
#
# 1 [IP] 1.decnz> [ZEROS] [REG BLOCK 1] 0010 [REG BLOCK 2]
# ->
# 5.root> 1 [break.1(IP)] [ZEROS] 0 [REG BLOCK 1] 010 [REG BLOCK 2]
#
# where IP          is the run length limited in 0s instruction pointer,
#       ZEROS       is a run of at least 2 0s,
#       REG BLOCK 1 starts and ends with 1s and has no runs of more than one 0,
#       REG BLOCK 2 is either empty or starts and ends with 1s and has no run of
#                   more than one 0.
#
# Both variants of DECNZ shift [REG BLOCK 1] over to the right one cell,
# thus providing more room for the IP. This is useful as the
# bootstrap does not leave enough room for the longest IP used by the larger
# machines.
#
# For all register operations, when going out to the regiser file a 1 is
# written to the tape after the IP so the end of the IP can be identified
# when returning back from the register file.
#
# DECNZ is implemented by:
#
# 1 [IP] 1.decnz> 0 [>0 0s] [REG BLOCK 1] 00 [REG] 0 [REG BLOCK 2]
# 1 [IP] 1 [>0 0s] 0 [updated REGS] 0 <1.ret1
# 5.root> 1 [break.0(IP)] 0 [>0 0s] 0 [updated REGS]
#
# or
#
# 1 [IP] 1.decnz> 0 [>0 0s] [REG BLOCK 1] 0 010 [REG BLOCK 2]
# 1 [IP] 1 [>0 0s] 0 [REG BLOCK 1] 0 <1.ret2 10 [REG BLOCK 2]
# 5.root> 1 [break.2(IP)] 0 [>0 0s] 0 [REG BLOCK 1] 010 [REG BLOCK 2]
#
# 1 [IP] 1.decnz> 0 [>0 0s]
# 1 [IP] 1 1.decnz.b> [>0 0s]
1.decnz 0 1 R 1.decnz.b
# with a 1 on the tape 1.decnz is actually 1.decnz.f
# used to skip past the last set 1 on a reg to
# check if it can be decremented
1.decnz 1 1 L 1.decnz.g
# 1 [IP] 1 1.decnz.b> [>0 0s] 1 [REST OF FIRST REG]
# 1 [IP] 1 [>0 0s] 0 1.decnz.c> [REST OF FIRST REG]
1.decnz.b 0 0 R 1.decnz.b
1.decnz.b 1 0 R 1.decnz.c
# 1.decnz.d> [REG] 0
# 0 [REG] decnz.d>
#
# but once we reach the 00 selector we transition into decrement:
#
# 1.decnz.d> 0
# 0 decnz.e>
1.decnz.c 0 1 R 1.decnz.d
1.decnz.c 1 1 R 1.decnz.c
1.decnz.d 0 0 R 1.decnz.e
1.decnz.d 1 0 R 1.decnz.c
1.decnz.e 0 0 L 1.decnz
# Find end of register to decrement:
# decnz.e> [1s] 1 0
# [1s] 1 <1.decnz 0
# [1s] <1.decnz.g 1 0
1.decnz.e 1 1 R 1.decnz.e
# If decnz.g does not find more of the register we cannot decrement:
# Use the alternate return, otherwise move to the right to prepare
# to overwrite the last digit.
1.decnz.g 0 0 L 2.ret2
1.decnz.g 1 1 R 1.decnz.h
# Increment the next register
# (We shift the registers by incrementing to the left then degrementing
# on the right)
1.decnz.h 0 1 R 1.decnz.i
# Decrement the last register:
1.decnz.h 1 0 R 1.decnz.h
# check if we've reached the end of the register file:
# If so we'll use 1.sel to remove the register we just added.
# Otherwise we will transition into decrementing the current register
# (Which will restore it to it's old value shifted one cell to the left.)
1.decnz.i 0 0 L 1.sel
1.decnz.i 1 1 R 1.decnz.e
#
1.inc 0 1 R 1.inc.b
1.inc.b 0 0 R 1.inc.b
1.inc.b 1 1 R 1.inc.c
1.inc.c 0 0 R 1.inc.d
1.inc.c 1 1 R 1.inc.c
1.inc.d 0 1 L 2.ret1
1.inc.d 1 1 R 1.inc.c
#
1.sel 0 1 R 1.sel.b
# with a 1 on the tape 1.sel is actually 1.decnz.j
# used to clear the extra register added after the RF
1.sel 1 0 L 2.ret1
1.sel.b 0 0 R 1.sel.b
1.sel.b 1 1 R 1.sel.c
1.sel.c 0 0 R 1.sel.d
1.sel.c 1 1 R 1.sel.c
1.sel.d 0 0 L 1.sel.e
1.sel.d 1 1 R 1.sel.c
1.sel.e 0 1 L 1.sel.f
1.sel.e 1 0 L 2.ret1
1.sel.f 0 0 R 1.sel.e
1.sel.f 1 1 L 1.sel.f
#
2.ret1 0 0 L 2.ret1.1
2.ret1 1 1 L 2.ret1
2.ret1.1 0 0 L 2.ret1.2
2.ret1.1 1 1 L 2.ret1
# search for the marker after IP
2.ret1.2 0 0 L 2.ret1.2
2.ret1.2 1 0 L 6.break.0
#
2.ret2 0 0 L 2.ret2.1
2.ret2 1 1 L 2.ret2
2.ret2.1 0 0 L 2.ret2.2
2.ret2.1 1 1 L 2.ret2
# search for the marker after IP
2.ret2.2 0 0 L 2.ret2.2
2.ret2.2 1 0 L 6.break.1
3.axiomcode.decnz 0 0 R 1.sel
3.axiomcode.decnz 1 1 R 3.wffstack.decnz
3.axiomcode.inc 0 0 R 1.sel
3.axiomcode.inc 1 1 R 3.wffstack.inc
3.nextproof.decnz 0 0 R 1.sel
3.nextproof.decnz 1 1 R 1.decnz
3.nextproof.inc 0 0 R 1.sel
3.nextproof.inc 1 1 R 1.inc
3.param1.decnz 0 0 R 1.sel
3.param1.decnz 1 1 R 3.axiomcode.decnz
3.param1.inc 0 0 R 1.sel
3.param1.inc 1 1 R 3.axiomcode.inc
3.param2.decnz 0 0 R 1.sel
3.param2.decnz 1 1 R 3.param1.decnz
3.param2.inc 0 0 R 1.sel
3.param2.inc 1 1 R 3.param1.inc
3.prooflist.decnz 0 0 R 1.sel
3.prooflist.decnz 1 1 R 3.scratch2.decnz
3.prooflist.inc 0 0 R 1.sel
3.prooflist.inc 1 1 R 3.scratch2.inc
3.scratch1.decnz 0 0 R 1.sel
3.scratch1.decnz 1 1 R 3.param2.decnz
3.scratch1.inc 0 0 R 1.sel
3.scratch1.inc 1 1 R 3.param2.inc
3.scratch2.decnz 0 0 R 1.sel
3.scratch2.decnz 1 1 R 3.scratch1.decnz
3.scratch2.inc 0 0 R 1.sel
3.scratch2.inc 1 1 R 3.scratch1.inc
3.topwff.decnz 0 0 R 1.sel
3.topwff.decnz 1 1 R 3.nextproof.decnz
3.topwff.inc 0 0 R 1.sel
3.topwff.inc 1 1 R 3.nextproof.inc
3.wffstack.decnz 0 0 R 1.sel
3.wffstack.decnz 1 1 R 3.topwff.decnz
3.wffstack.inc 0 0 R 1.sel
3.wffstack.inc 1 1 R 3.topwff.inc
#
# 4. dispatch
#
# Find the start of the IP. We pass by a set number of 0 cells going
# left (how many depends on the decision tree), then scan right for the
# first 1 cell.
#
4.dispatch.1 0 0 L 4.dispatch.2
4.dispatch.1 1 1 L 6.continue.0
4.dispatch.2 0 0 L 4.dispatch.3
4.dispatch.2 1 1 L 6.continue.0
4.dispatch.3 0 0 L 4.dispatch.4
4.dispatch.3 1 1 L 6.continue.0
4.dispatch.4 0 0 L 4.dispatch.5
4.dispatch.4 1 1 L 6.continue.0
4.dispatch.5 0 0 L 4.dispatch.6
4.dispatch.5 1 1 L 6.continue.0
4.dispatch.6 0 0 L 4.dispatch.7
4.dispatch.6 1 1 L 6.continue.0
4.dispatch.7 0 0 R 5.root
4.dispatch.7 1 1 L 6.continue.0
#
# 5. root - find the root of the IP
#
# There is no special handling to call main() in a loop. At the end
# of main() the IP simply overflows past the marker to the left of the
# IP and creates a new marker with the IP all zeros.
#
5.root 0 0 R 5.root
5.root 1 1 R main().0
#
# 6. IP jump instructions.
#
6.break.0 0 1 L 6.continue.0
6.break.0 1 0 L 6.break.0
6.break.1 0 0 L 6.break.0
6.break.1 1 0 L 6.break.1
6.continue.0 0 0 L 4.dispatch.1
6.continue.0 1 1 L 6.continue.0
6.continue.1 0 0 L 6.continue.1
6.continue.1 1 0 L 6.continue.0
6.continue.2 0 0 L 6.continue.2
6.continue.2 1 0 L 6.continue.1
6.continue.3 0 0 L 6.continue.3
6.continue.3 1 0 L 6.continue.2
6.continue.4 0 0 L 6.continue.4
6.continue.4 1 0 L 6.continue.3
main().0 0 0 R prefix_source_8
main().0 1 1 R prefix_source_200
prefix_source_0 0 0 R 3.prooflist.decnz
prefix_source_0 1 0 L 6.break.1
prefix_source_1 0 0 R 3.scratch1.inc
prefix_source_1 1 0 L 6.continue.2
prefix_source_10 0 0 R 3.scratch1.inc
prefix_source_10 1 0 L 6.continue.1
prefix_source_100 0 0 R prefix_source_46
prefix_source_100 1 1 R 3.param2.inc
prefix_source_101 0 0 R prefix_source_99
prefix_source_101 1 1 R prefix_source_100
prefix_source_102 0 0 R 3.scratch1.decnz
prefix_source_102 1 1 R prefix_source_101
prefix_source_103 0 0 R 3.param2.decnz
prefix_source_103 1 0 L 6.continue.0
prefix_source_104 0 0 R prefix_source_103
prefix_source_104 1 0 L 6.break.1
prefix_source_105 0 0 R 3.param2.decnz
prefix_source_105 1 1 R prefix_source_104
prefix_source_106 0 0 R prefix_source_102
prefix_source_106 1 1 R prefix_source_105
prefix_source_107 0 0 R 3.topwff.decnz
prefix_source_107 1 0 L 6.continue.0
prefix_source_108 0 0 R prefix_source_106
prefix_source_108 1 1 R prefix_source_107
prefix_source_109 0 0 R 3.param1.decnz
prefix_source_109 1 1 R prefix_source_45
prefix_source_11 0 0 R 3.scratch2.decnz
prefix_source_11 1 1 R prefix_source_10
prefix_source_110 0 0 R prefix_source_109
prefix_source_110 1 1 R prefix_source_108
prefix_source_111 0 0 R prefix_source_11
prefix_source_111 1 1 R prefix_source_110
prefix_source_112 0 0 R prefix_source_108
prefix_source_112 1 1 R prefix_source_111
prefix_source_113 0 0 R prefix_source_98
prefix_source_113 1 1 R prefix_source_112
prefix_source_114 0 0 R prefix_source_92
prefix_source_114 1 1 R prefix_source_113
prefix_source_115 0 0 R prefix_source_94
prefix_source_115 1 1 R prefix_source_114
prefix_source_116 0 0 R prefix_source_88
prefix_source_116 1 1 R prefix_source_115
prefix_source_117 0 0 R prefix_source_97
prefix_source_117 1 1 R prefix_source_116
prefix_source_118 0 0 R prefix_source_92
prefix_source_118 1 1 R prefix_source_117
prefix_source_119 0 0 R prefix_source_80
prefix_source_119 1 1 R prefix_source_118
prefix_source_12 0 0 R prefix_source_9
prefix_source_12 1 1 R prefix_source_11
prefix_source_120 0 0 R prefix_source_71
prefix_source_120 1 1 R prefix_source_119
prefix_source_121 0 0 R prefix_source_71
prefix_source_121 1 1 R prefix_source_120
prefix_source_122 0 0 R prefix_source_90
prefix_source_122 1 1 R prefix_source_121
prefix_source_123 0 0 R prefix_source_97
prefix_source_123 1 1 R prefix_source_122
prefix_source_124 0 0 R prefix_source_64
prefix_source_124 1 1 R prefix_source_123
prefix_source_125 0 0 R prefix_source_80
prefix_source_125 1 1 R prefix_source_124
prefix_source_126 0 0 R prefix_source_85
prefix_source_126 1 1 R prefix_source_125
prefix_source_127 0 0 R prefix_source_96
prefix_source_127 1 1 R prefix_source_126
prefix_source_128 0 0 R prefix_source_96
prefix_source_128 1 1 R prefix_source_127
prefix_source_129 0 0 R prefix_source_80
prefix_source_129 1 1 R prefix_source_128
prefix_source_13 0 0 R prefix_source_12
prefix_source_13 1 0 L 6.continue.2
prefix_source_130 0 0 R prefix_source_88
prefix_source_130 1 1 R prefix_source_129
prefix_source_131 0 0 R prefix_source_84
prefix_source_131 1 1 R prefix_source_130
prefix_source_132 0 0 R prefix_source_86
prefix_source_132 1 1 R prefix_source_131
prefix_source_133 0 0 R prefix_source_71
prefix_source_133 1 1 R prefix_source_132
prefix_source_134 0 0 R prefix_source_63
prefix_source_134 1 1 R prefix_source_133
prefix_source_135 0 0 R prefix_source_88
prefix_source_135 1 1 R prefix_source_134
prefix_source_136 0 0 R prefix_source_87
prefix_source_136 1 1 R prefix_source_135
prefix_source_137 0 0 R prefix_source_63
prefix_source_137 1 1 R prefix_source_136
prefix_source_138 0 0 R prefix_source_90
prefix_source_138 1 1 R prefix_source_137
prefix_source_139 0 0 R prefix_source_65
prefix_source_139 1 1 R prefix_source_138
prefix_source_14 0 0 R 3.scratch2.inc
prefix_source_14 1 1 R prefix_source_13
prefix_source_140 0 0 R prefix_source_58
prefix_source_140 1 1 R prefix_source_139
prefix_source_141 0 0 R prefix_source_68
prefix_source_141 1 1 R prefix_source_140
prefix_source_142 0 0 R prefix_source_63
prefix_source_142 1 1 R prefix_source_141
prefix_source_143 0 0 R prefix_source_82
prefix_source_143 1 1 R prefix_source_142
prefix_source_144 0 0 R prefix_source_89
prefix_source_144 1 1 R prefix_source_143
prefix_source_145 0 0 R prefix_source_63
prefix_source_145 1 1 R prefix_source_144
prefix_source_146 0 0 R prefix_source_89
prefix_source_146 1 1 R prefix_source_145
prefix_source_147 0 0 R prefix_source_78
prefix_source_147 1 1 R prefix_source_146
prefix_source_148 0 0 R prefix_source_68
prefix_source_148 1 1 R prefix_source_147
prefix_source_149 0 0 R prefix_source_73
prefix_source_149 1 1 R prefix_source_148
prefix_source_15 0 0 R 3.prooflist.decnz
prefix_source_15 1 1 R prefix_source_14
prefix_source_150 0 0 R prefix_source_74
prefix_source_150 1 1 R prefix_source_149
prefix_source_151 0 0 R prefix_source_59
prefix_source_151 1 1 R prefix_source_150
prefix_source_152 0 0 R prefix_source_88
prefix_source_152 1 1 R prefix_source_151
prefix_source_153 0 0 R prefix_source_81
prefix_source_153 1 1 R prefix_source_152
prefix_source_154 0 0 R prefix_source_87
prefix_source_154 1 1 R prefix_source_153
prefix_source_155 0 0 R prefix_source_82
prefix_source_155 1 1 R prefix_source_154
prefix_source_156 0 0 R prefix_source_74
prefix_source_156 1 1 R prefix_source_155
prefix_source_157 0 0 R prefix_source_48
prefix_source_157 1 1 R prefix_source_156
prefix_source_158 0 0 R prefix_source_58
prefix_source_158 1 1 R prefix_source_157
prefix_source_159 0 0 R prefix_source_58
prefix_source_159 1 1 R prefix_source_158
prefix_source_16 0 0 R 3.prooflist.inc
prefix_source_16 1 0 L 6.continue.1
prefix_source_160 0 0 R prefix_source_81
prefix_source_160 1 1 R prefix_source_159
prefix_source_161 0 0 R prefix_source_80
prefix_source_161 1 1 R prefix_source_160
prefix_source_162 0 0 R prefix_source_79
prefix_source_162 1 1 R prefix_source_161
prefix_source_163 0 0 R prefix_source_70
prefix_source_163 1 1 R prefix_source_162
prefix_source_164 0 0 R prefix_source_63
prefix_source_164 1 1 R prefix_source_163
prefix_source_165 0 0 R prefix_source_78
prefix_source_165 1 1 R prefix_source_164
prefix_source_166 0 0 R prefix_source_74
prefix_source_166 1 1 R prefix_source_165
prefix_source_167 0 0 R prefix_source_73
prefix_source_167 1 1 R prefix_source_166
prefix_source_168 0 0 R prefix_source_67
prefix_source_168 1 1 R prefix_source_167
prefix_source_169 0 0 R prefix_source_71
prefix_source_169 1 1 R prefix_source_168
prefix_source_17 0 0 R 3.scratch2.decnz
prefix_source_17 1 1 R prefix_source_16
prefix_source_170 0 0 R prefix_source_67
prefix_source_170 1 1 R prefix_source_169
prefix_source_171 0 0 R prefix_source_70
prefix_source_171 1 1 R prefix_source_170
prefix_source_172 0 0 R prefix_source_57
prefix_source_172 1 1 R prefix_source_171
prefix_source_173 0 0 R prefix_source_66
prefix_source_173 1 1 R prefix_source_172
prefix_source_174 0 0 R prefix_source_30
prefix_source_174 1 1 R prefix_source_173
prefix_source_175 0 0 R prefix_source_18
prefix_source_175 1 1 R prefix_source_174
prefix_source_176 0 0 R prefix_source_39
prefix_source_176 1 1 R prefix_source_175
prefix_source_177 0 0 R prefix_source_66
prefix_source_177 1 1 R prefix_source_176
prefix_source_178 0 0 R prefix_source_65
prefix_source_178 1 1 R prefix_source_177
prefix_source_179 0 0 R prefix_source_65
prefix_source_179 1 1 R prefix_source_178
prefix_source_18 0 0 R prefix_source_15
prefix_source_18 1 1 R prefix_source_17
prefix_source_180 0 0 R prefix_source_64
prefix_source_180 1 1 R prefix_source_179
prefix_source_181 0 0 R prefix_source_60
prefix_source_181 1 1 R prefix_source_180
prefix_source_182 0 0 R prefix_source_59
prefix_source_182 1 1 R prefix_source_181
prefix_source_183 0 0 R prefix_source_182
prefix_source_183 1 0 L 6.break.1
prefix_source_184 0 0 R 3.axiomcode.decnz
prefix_source_184 1 1 R prefix_source_183
prefix_source_185 0 0 R prefix_source_106
prefix_source_185 1 1 R halt
prefix_source_186 0 0 R prefix_source_51
prefix_source_186 1 1 R prefix_source_46
prefix_source_187 0 0 R prefix_source_185
prefix_source_187 1 1 R prefix_source_186
prefix_source_188 0 0 R 3.scratch1.inc
prefix_source_188 1 1 R prefix_source_187
prefix_source_189 0 0 R prefix_source_184
prefix_source_189 1 1 R prefix_source_188
prefix_source_19 0 0 R 3.axiomcode.inc
prefix_source_19 1 0 L 6.continue.1
prefix_source_190 0 0 R prefix_source_189
prefix_source_190 1 0 L 6.break.1
prefix_source_191 0 0 R 3.axiomcode.decnz
prefix_source_191 1 1 R prefix_source_190
prefix_source_192 0 0 R prefix_source_191
prefix_source_192 1 1 R prefix_source_48
prefix_source_193 0 0 R prefix_source_192
prefix_source_193 1 0 L 6.break.1
prefix_source_194 0 0 R 3.axiomcode.decnz
prefix_source_194 1 1 R prefix_source_193
prefix_source_195 0 0 R prefix_source_66
prefix_source_195 1 1 R prefix_source_25
prefix_source_196 0 0 R prefix_source_106
prefix_source_196 1 1 R prefix_source_43
prefix_source_197 0 0 R prefix_source_195
prefix_source_197 1 1 R prefix_source_196
prefix_source_198 0 0 R prefix_source_194
prefix_source_198 1 1 R prefix_source_197
prefix_source_199 0 0 R prefix_source_24
prefix_source_199 1 1 R prefix_source_198
prefix_source_2 0 0 R 3.prooflist.inc
prefix_source_2 1 1 R prefix_source_1
prefix_source_20 0 0 R 3.scratch1.decnz
prefix_source_20 1 1 R prefix_source_19
prefix_source_200 0 0 R prefix_source_21
prefix_source_200 1 1 R prefix_source_199
prefix_source_21 0 0 R prefix_source_18
prefix_source_21 1 1 R prefix_source_20
prefix_source_22 0 0 R 3.param1.inc
prefix_source_22 1 0 L 6.continue.1
prefix_source_23 0 0 R 3.scratch1.decnz
prefix_source_23 1 1 R prefix_source_22
prefix_source_24 0 0 R prefix_source_18
prefix_source_24 1 1 R prefix_source_23
prefix_source_25 0 0 R 3.topwff.decnz
prefix_source_25 1 1 R prefix_source_10
prefix_source_26 0 0 R 3.topwff.inc
prefix_source_26 1 0 L 6.continue.1
prefix_source_27 0 0 R 3.wffstack.decnz
prefix_source_27 1 1 R prefix_source_26
prefix_source_28 0 0 R 3.scratch2.inc
prefix_source_28 1 1 R prefix_source_1
prefix_source_29 0 0 R 3.topwff.decnz
prefix_source_29 1 1 R prefix_source_28
prefix_source_3 0 0 R 3.nextproof.decnz
prefix_source_3 1 1 R prefix_source_2
prefix_source_30 0 0 R 3.scratch1.decnz
prefix_source_30 1 1 R prefix_source_26
prefix_source_31 0 0 R 3.scratch2.inc
prefix_source_31 1 1 R prefix_source_30
prefix_source_32 0 0 R prefix_source_31
prefix_source_32 1 0 L 6.continue.2
prefix_source_33 0 0 R 3.scratch1.decnz
prefix_source_33 1 1 R prefix_source_32
prefix_source_34 0 0 R prefix_source_29
prefix_source_34 1 1 R prefix_source_33
prefix_source_35 0 0 R 3.wffstack.inc
prefix_source_35 1 0 L 6.continue.1
prefix_source_36 0 0 R 3.scratch2.decnz
prefix_source_36 1 1 R prefix_source_35
prefix_source_37 0 0 R prefix_source_34
prefix_source_37 1 1 R prefix_source_36
prefix_source_38 0 0 R prefix_source_27
prefix_source_38 1 1 R prefix_source_37
prefix_source_39 0 0 R prefix_source_25
prefix_source_39 1 1 R prefix_source_38
prefix_source_4 0 0 R 3.nextproof.inc
prefix_source_4 1 0 L 6.continue.1
prefix_source_40 0 0 R 3.topwff.inc
prefix_source_40 1 1 R prefix_source_1
prefix_source_41 0 0 R 3.param1.decnz
prefix_source_41 1 1 R prefix_source_40
prefix_source_42 0 0 R prefix_source_41
prefix_source_42 1 1 R prefix_source_23
prefix_source_43 0 0 R prefix_source_39
prefix_source_43 1 1 R prefix_source_42
prefix_source_44 0 0 R 3.param2.decnz
prefix_source_44 1 1 R prefix_source_40
prefix_source_45 0 0 R 3.param2.inc
prefix_source_45 1 0 L 6.continue.1
prefix_source_46 0 0 R 3.scratch1.decnz
prefix_source_46 1 1 R prefix_source_45
prefix_source_47 0 0 R prefix_source_44
prefix_source_47 1 1 R prefix_source_46
prefix_source_48 0 0 R prefix_source_39
prefix_source_48 1 1 R prefix_source_47
prefix_source_49 0 0 R prefix_source_43
prefix_source_49 1 1 R prefix_source_48
prefix_source_5 0 0 R 3.scratch1.decnz
prefix_source_5 1 1 R prefix_source_4
prefix_source_50 0 0 R 3.wffstack.decnz
prefix_source_50 1 1 R prefix_source_14
prefix_source_51 0 0 R prefix_source_50
prefix_source_51 1 1 R prefix_source_36
prefix_source_52 0 0 R 3.topwff.inc
prefix_source_52 1 1 R 3.topwff.inc
prefix_source_53 0 0 R prefix_source_52
prefix_source_53 1 1 R prefix_source_52
prefix_source_54 0 0 R prefix_source_53
prefix_source_54 1 0 L 6.continue.1
prefix_source_55 0 0 R 3.scratch2.decnz
prefix_source_55 1 1 R prefix_source_54
prefix_source_56 0 0 R prefix_source_34
prefix_source_56 1 1 R prefix_source_55
prefix_source_57 0 0 R prefix_source_51
prefix_source_57 1 1 R prefix_source_56
prefix_source_58 0 0 R prefix_source_57
prefix_source_58 1 1 R prefix_source_52
prefix_source_59 0 0 R prefix_source_49
prefix_source_59 1 1 R prefix_source_58
prefix_source_6 0 0 R prefix_source_5
prefix_source_6 1 1 R 3.nextproof.inc
prefix_source_60 0 0 R prefix_source_18
prefix_source_60 1 1 R prefix_source_46
prefix_source_61 0 0 R 3.axiomcode.decnz
prefix_source_61 1 1 R prefix_source_40
prefix_source_62 0 0 R prefix_source_61
prefix_source_62 1 1 R prefix_source_20
prefix_source_63 0 0 R prefix_source_39
prefix_source_63 1 1 R prefix_source_62
prefix_source_64 0 0 R prefix_source_43
prefix_source_64 1 1 R prefix_source_63
prefix_source_65 0 0 R prefix_source_57
prefix_source_65 1 1 R prefix_source_48
prefix_source_66 0 0 R prefix_source_43
prefix_source_66 1 1 R prefix_source_57
prefix_source_67 0 0 R prefix_source_58
prefix_source_67 1 1 R 3.topwff.inc
prefix_source_68 0 0 R prefix_source_49
prefix_source_68 1 1 R prefix_source_67
prefix_source_69 0 0 R prefix_source_57
prefix_source_69 1 1 R prefix_source_68
prefix_source_7 0 0 R prefix_source_3
prefix_source_7 1 1 R prefix_source_6
prefix_source_70 0 0 R prefix_source_69
prefix_source_70 1 1 R prefix_source_64
prefix_source_71 0 0 R prefix_source_48
prefix_source_71 1 1 R prefix_source_63
prefix_source_72 0 0 R prefix_source_57
prefix_source_72 1 1 R prefix_source_57
prefix_source_73 0 0 R prefix_source_72
prefix_source_73 1 1 R prefix_source_43
prefix_source_74 0 0 R prefix_source_64
prefix_source_74 1 1 R prefix_source_58
prefix_source_75 0 0 R prefix_source_39
prefix_source_75 1 1 R 3.topwff.inc
prefix_source_76 0 0 R prefix_source_75
prefix_source_76 1 1 R prefix_source_57
prefix_source_77 0 0 R prefix_source_58
prefix_source_77 1 1 R prefix_source_76
prefix_source_78 0 0 R prefix_source_76
prefix_source_78 1 1 R prefix_source_77
prefix_source_79 0 0 R prefix_source_57
prefix_source_79 1 1 R 3.topwff.inc
prefix_source_8 0 0 R prefix_source_0
prefix_source_8 1 1 R prefix_source_7
prefix_source_80 0 0 R prefix_source_71
prefix_source_80 1 1 R prefix_source_79
prefix_source_81 0 0 R prefix_source_73
prefix_source_81 1 1 R prefix_source_71
prefix_source_82 0 0 R prefix_source_58
prefix_source_82 1 1 R prefix_source_69
prefix_source_83 0 0 R prefix_source_63
prefix_source_83 1 1 R prefix_source_43
prefix_source_84 0 0 R prefix_source_83
prefix_source_84 1 1 R prefix_source_79
prefix_source_85 0 0 R prefix_source_63
prefix_source_85 1 1 R prefix_source_48
prefix_source_86 0 0 R prefix_source_85
prefix_source_86 1 1 R prefix_source_79
prefix_source_87 0 0 R prefix_source_84
prefix_source_87 1 1 R prefix_source_86
prefix_source_88 0 0 R prefix_source_57
prefix_source_88 1 1 R prefix_source_58
prefix_source_89 0 0 R prefix_source_49
prefix_source_89 1 1 R prefix_source_79
prefix_source_9 0 0 R 3.scratch1.decnz
prefix_source_9 1 0 L 6.break.1
prefix_source_90 0 0 R prefix_source_43
prefix_source_90 1 1 R prefix_source_89
prefix_source_91 0 0 R prefix_source_57
prefix_source_91 1 1 R prefix_source_76
prefix_source_92 0 0 R prefix_source_76
prefix_source_92 1 1 R prefix_source_91
prefix_source_93 0 0 R prefix_source_78
prefix_source_93 1 1 R prefix_source_92
prefix_source_94 0 0 R prefix_source_92
prefix_source_94 1 1 R prefix_source_93
prefix_source_95 0 0 R prefix_source_86
prefix_source_95 1 1 R prefix_source_94
prefix_source_96 0 0 R prefix_source_88
prefix_source_96 1 1 R prefix_source_95
prefix_source_97 0 0 R prefix_source_78
prefix_source_97 1 1 R prefix_source_88
prefix_source_98 0 0 R 3.axiomcode.decnz
prefix_source_98 1 1 R prefix_source_28
prefix_source_99 0 0 R 3.param2.decnz
prefix_source_99 1 0 L 6.continue.1
