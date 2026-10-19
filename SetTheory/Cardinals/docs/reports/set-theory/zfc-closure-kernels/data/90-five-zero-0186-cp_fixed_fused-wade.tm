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
codec_0.0 0 0 R 3.scratch1.inc
codec_0.0 1 0 L 6.continue.1
codec_1.0 0 0 R 3.topwff.decnz
codec_1.0 1 1 R codec_0.0
codec_10.0 0 0 R 3.scratch1.decnz
codec_10.0 1 1 R codec_9.0
codec_100.0 0 0 R 3.param2.decnz
codec_100.0 1 0 L 6.continue.1
codec_101.0 0 0 R codec_26.0
codec_101.0 1 1 R 3.param2.inc
codec_102.0 0 0 R codec_100.0
codec_102.0 1 1 R codec_101.0
codec_103.0 0 0 R 3.scratch1.decnz
codec_103.0 1 1 R codec_102.0
codec_104.0 0 0 R 3.param2.decnz
codec_104.0 1 0 L 6.continue.0
codec_105.0 0 0 R codec_104.0
codec_105.0 1 0 L 6.break.1
codec_106.0 0 0 R 3.param2.decnz
codec_106.0 1 1 R codec_105.0
codec_107.0 0 0 R codec_103.0
codec_107.0 1 1 R codec_106.0
codec_108.0 0 0 R 3.topwff.decnz
codec_108.0 1 0 L 6.continue.0
codec_109.0 0 0 R codec_107.0
codec_109.0 1 1 R codec_108.0
codec_11.0 0 0 R codec_6.0
codec_11.0 1 1 R codec_10.0
codec_110.0 0 0 R 3.param1.decnz
codec_110.0 1 1 R codec_25.0
codec_111.0 0 0 R codec_110.0
codec_111.0 1 1 R codec_109.0
codec_112.0 0 0 R codec_39.0
codec_112.0 1 1 R codec_111.0
codec_113.0 0 0 R codec_109.0
codec_113.0 1 1 R codec_112.0
codec_114.0 0 0 R codec_99.0
codec_114.0 1 1 R codec_113.0
codec_115.0 0 0 R codec_88.0
codec_115.0 1 1 R codec_114.0
codec_116.0 0 0 R codec_88.0
codec_116.0 1 1 R codec_115.0
codec_117.0 0 0 R codec_51.0
codec_117.0 1 1 R codec_116.0
codec_118.0 0 0 R codec_52.0
codec_118.0 1 1 R codec_117.0
codec_119.0 0 0 R codec_98.0
codec_119.0 1 1 R codec_118.0
codec_12.0 0 0 R 3.wffstack.inc
codec_12.0 1 0 L 6.continue.1
codec_120.0 0 0 R codec_83.0
codec_120.0 1 1 R codec_119.0
codec_121.0 0 0 R codec_75.0
codec_121.0 1 1 R codec_120.0
codec_122.0 0 0 R codec_97.0
codec_122.0 1 1 R codec_121.0
codec_123.0 0 0 R codec_23.0
codec_123.0 1 1 R codec_122.0
codec_124.0 0 0 R codec_88.0
codec_124.0 1 1 R codec_123.0
codec_125.0 0 0 R codec_89.0
codec_125.0 1 1 R codec_124.0
codec_126.0 0 0 R codec_95.0
codec_126.0 1 1 R codec_125.0
codec_127.0 0 0 R codec_59.0
codec_127.0 1 1 R codec_126.0
codec_128.0 0 0 R codec_94.0
codec_128.0 1 1 R codec_127.0
codec_129.0 0 0 R codec_28.0
codec_129.0 1 1 R codec_128.0
codec_13.0 0 0 R 3.scratch2.decnz
codec_13.0 1 1 R codec_12.0
codec_130.0 0 0 R codec_85.0
codec_130.0 1 1 R codec_129.0
codec_131.0 0 0 R codec_95.0
codec_131.0 1 1 R codec_130.0
codec_132.0 0 0 R codec_88.0
codec_132.0 1 1 R codec_131.0
codec_133.0 0 0 R codec_94.0
codec_133.0 1 1 R codec_132.0
codec_134.0 0 0 R codec_92.0
codec_134.0 1 1 R codec_133.0
codec_135.0 0 0 R codec_90.0
codec_135.0 1 1 R codec_134.0
codec_136.0 0 0 R codec_33.0
codec_136.0 1 1 R codec_135.0
codec_137.0 0 0 R codec_52.0
codec_137.0 1 1 R codec_136.0
codec_138.0 0 0 R codec_89.0
codec_138.0 1 1 R codec_137.0
codec_139.0 0 0 R codec_74.0
codec_139.0 1 1 R codec_138.0
codec_14.0 0 0 R codec_11.0
codec_14.0 1 1 R codec_13.0
codec_140.0 0 0 R codec_35.0
codec_140.0 1 1 R codec_139.0
codec_141.0 0 0 R codec_36.0
codec_141.0 1 1 R codec_140.0
codec_142.0 0 0 R codec_85.0
codec_142.0 1 1 R codec_141.0
codec_143.0 0 0 R codec_89.0
codec_143.0 1 1 R codec_142.0
codec_144.0 0 0 R codec_74.0
codec_144.0 1 1 R codec_143.0
codec_145.0 0 0 R codec_35.0
codec_145.0 1 1 R codec_144.0
codec_146.0 0 0 R codec_36.0
codec_146.0 1 1 R codec_145.0
codec_147.0 0 0 R codec_52.0
codec_147.0 1 1 R codec_146.0
codec_148.0 0 0 R codec_88.0
codec_148.0 1 1 R codec_147.0
codec_149.0 0 0 R codec_51.0
codec_149.0 1 1 R codec_148.0
codec_15.0 0 0 R codec_3.0
codec_15.0 1 1 R codec_14.0
codec_150.0 0 0 R codec_74.0
codec_150.0 1 1 R codec_149.0
codec_151.0 0 0 R codec_36.0
codec_151.0 1 1 R codec_150.0
codec_152.0 0 0 R codec_16.0
codec_152.0 1 1 R codec_151.0
codec_153.0 0 0 R codec_86.0
codec_153.0 1 1 R codec_152.0
codec_154.0 0 0 R codec_34.0
codec_154.0 1 1 R codec_153.0
codec_155.0 0 0 R codec_36.0
codec_155.0 1 1 R codec_154.0
codec_156.0 0 0 R codec_74.0
codec_156.0 1 1 R codec_155.0
codec_157.0 0 0 R codec_16.0
codec_157.0 1 1 R codec_156.0
codec_158.0 0 0 R codec_36.0
codec_158.0 1 1 R codec_157.0
codec_159.0 0 0 R codec_36.0
codec_159.0 1 1 R codec_158.0
codec_16.0 0 0 R codec_1.0
codec_16.0 1 1 R codec_15.0
codec_160.0 0 0 R codec_51.0
codec_160.0 1 1 R codec_159.0
codec_161.0 0 0 R codec_74.0
codec_161.0 1 1 R codec_160.0
codec_162.0 0 0 R codec_35.0
codec_162.0 1 1 R codec_161.0
codec_163.0 0 0 R codec_16.0
codec_163.0 1 1 R codec_162.0
codec_164.0 0 0 R codec_74.0
codec_164.0 1 1 R codec_163.0
codec_165.0 0 0 R codec_34.0
codec_165.0 1 1 R codec_164.0
codec_166.0 0 0 R codec_16.0
codec_166.0 1 1 R codec_165.0
codec_167.0 0 0 R codec_16.0
codec_167.0 1 1 R codec_166.0
codec_168.0 0 0 R codec_36.0
codec_168.0 1 1 R codec_167.0
codec_169.0 0 0 R codec_74.0
codec_169.0 1 1 R codec_168.0
codec_17.0 0 0 R 3.scratch1.inc
codec_17.0 1 1 R 3.topwff.inc
codec_170.0 0 0 R codec_35.0
codec_170.0 1 1 R codec_169.0
codec_171.0 0 0 R codec_34.0
codec_171.0 1 1 R codec_170.0
codec_172.0 0 0 R codec_34.0
codec_172.0 1 1 R codec_171.0
codec_173.0 0 0 R codec_35.0
codec_173.0 1 1 R codec_172.0
codec_174.0 0 0 R codec_36.0
codec_174.0 1 1 R codec_173.0
codec_175.0 0 0 R codec_72.0
codec_175.0 1 1 R codec_174.0
codec_176.0 0 0 R codec_62.0
codec_176.0 1 1 R codec_175.0
codec_177.0 0 0 R codec_69.0
codec_177.0 1 1 R codec_176.0
codec_178.0 0 0 R codec_80.0
codec_178.0 1 1 R codec_177.0
codec_179.0 0 0 R codec_53.0
codec_179.0 1 1 R codec_178.0
codec_18.0 0 0 R codec_17.0
codec_18.0 1 0 L 6.continue.1
codec_180.0 0 0 R codec_85.0
codec_180.0 1 1 R codec_179.0
codec_181.0 0 0 R codec_79.0
codec_181.0 1 1 R codec_180.0
codec_182.0 0 0 R codec_84.0
codec_182.0 1 1 R codec_181.0
codec_183.0 0 0 R codec_83.0
codec_183.0 1 1 R codec_182.0
codec_184.0 0 0 R codec_80.0
codec_184.0 1 1 R codec_183.0
codec_185.0 0 0 R codec_28.0
codec_185.0 1 1 R codec_184.0
codec_186.0 0 0 R codec_52.0
codec_186.0 1 1 R codec_185.0
codec_187.0 0 0 R codec_52.0
codec_187.0 1 1 R codec_186.0
codec_188.0 0 0 R codec_79.0
codec_188.0 1 1 R codec_187.0
codec_189.0 0 0 R codec_23.0
codec_189.0 1 1 R codec_188.0
codec_19.0 0 0 R 3.param1.decnz
codec_19.0 1 1 R codec_18.0
codec_190.0 0 0 R codec_74.0
codec_190.0 1 1 R codec_189.0
codec_191.0 0 0 R codec_66.0
codec_191.0 1 1 R codec_190.0
codec_192.0 0 0 R codec_73.0
codec_192.0 1 1 R codec_191.0
codec_193.0 0 0 R codec_52.0
codec_193.0 1 1 R codec_192.0
codec_194.0 0 0 R codec_69.0
codec_194.0 1 1 R codec_193.0
codec_195.0 0 0 R codec_62.0
codec_195.0 1 1 R codec_194.0
codec_196.0 0 0 R codec_37.0
codec_196.0 1 1 R codec_195.0
codec_197.0 0 0 R codec_62.0
codec_197.0 1 1 R codec_196.0
codec_198.0 0 0 R codec_66.0
codec_198.0 1 1 R codec_197.0
codec_199.0 0 0 R codec_51.0
codec_199.0 1 1 R codec_198.0
codec_2.0 0 0 R 3.topwff.inc
codec_2.0 1 0 L 6.continue.1
codec_20.0 0 0 R 3.param1.inc
codec_20.0 1 0 L 6.continue.1
codec_200.0 0 0 R codec_60.0
codec_200.0 1 1 R codec_199.0
codec_201.0 0 0 R codec_28.0
codec_201.0 1 1 R codec_200.0
codec_202.0 0 0 R codec_51.0
codec_202.0 1 1 R codec_201.0
codec_203.0 0 0 R codec_59.0
codec_203.0 1 1 R codec_202.0
codec_204.0 0 0 R codec_51.0
codec_204.0 1 1 R codec_203.0
codec_205.0 0 0 R codec_23.0
codec_205.0 1 1 R codec_204.0
codec_206.0 0 0 R codec_51.0
codec_206.0 1 1 R codec_205.0
codec_207.0 0 0 R codec_7.0
codec_207.0 1 1 R codec_206.0
codec_208.0 0 0 R codec_57.0
codec_208.0 1 1 R codec_207.0
codec_209.0 0 0 R codec_16.0
codec_209.0 1 1 R codec_208.0
codec_21.0 0 0 R 3.scratch1.decnz
codec_21.0 1 1 R codec_20.0
codec_210.0 0 0 R codec_33.0
codec_210.0 1 1 R codec_209.0
codec_211.0 0 0 R codec_58.0
codec_211.0 1 1 R codec_210.0
codec_212.0 0 0 R codec_53.0
codec_212.0 1 1 R codec_211.0
codec_213.0 0 0 R 3.prooflist.decnz
codec_213.0 1 0 L 6.break.1
codec_214.0 0 0 R 3.prooflist.inc
codec_214.0 1 1 R 3.scratch1.inc
codec_215.0 0 0 R codec_214.0
codec_215.0 1 0 L 6.continue.1
codec_216.0 0 0 R 3.nextproof.decnz
codec_216.0 1 1 R codec_215.0
codec_217.0 0 0 R 3.nextproof.inc
codec_217.0 1 0 L 6.continue.1
codec_218.0 0 0 R 3.scratch1.decnz
codec_218.0 1 1 R codec_217.0
codec_219.0 0 0 R codec_218.0
codec_219.0 1 1 R 3.nextproof.inc
codec_22.0 0 0 R codec_19.0
codec_22.0 1 1 R codec_21.0
codec_220.0 0 0 R codec_216.0
codec_220.0 1 1 R codec_219.0
codec_221.0 0 0 R codec_213.0
codec_221.0 1 1 R codec_220.0
codec_222.0 0 0 R codec_57.0
codec_222.0 1 1 R codec_31.0
codec_223.0 0 0 R codec_57.0
codec_223.0 1 1 R codec_21.0
codec_224.0 0 0 R codec_212.0
codec_224.0 1 0 L 6.break.1
codec_225.0 0 0 R 3.axiomcode.decnz
codec_225.0 1 1 R codec_224.0
codec_226.0 0 0 R codec_107.0
codec_226.0 1 1 R halt
codec_227.0 0 0 R codec_44.0
codec_227.0 1 1 R codec_26.0
codec_228.0 0 0 R codec_226.0
codec_228.0 1 1 R codec_227.0
codec_229.0 0 0 R 3.scratch1.inc
codec_229.0 1 1 R codec_228.0
codec_23.0 0 0 R codec_16.0
codec_23.0 1 1 R codec_22.0
codec_230.0 0 0 R codec_225.0
codec_230.0 1 1 R codec_229.0
codec_231.0 0 0 R codec_230.0
codec_231.0 1 0 L 6.break.1
codec_232.0 0 0 R 3.axiomcode.decnz
codec_232.0 1 1 R codec_231.0
codec_233.0 0 0 R codec_232.0
codec_233.0 1 1 R codec_28.0
codec_234.0 0 0 R codec_233.0
codec_234.0 1 0 L 6.break.1
codec_235.0 0 0 R 3.axiomcode.decnz
codec_235.0 1 1 R codec_234.0
codec_236.0 0 0 R codec_23.0
codec_236.0 1 1 R codec_51.0
codec_237.0 0 0 R codec_107.0
codec_237.0 1 1 R codec_23.0
codec_238.0 0 0 R codec_1.0
codec_238.0 1 1 R codec_237.0
codec_239.0 0 0 R codec_236.0
codec_239.0 1 1 R codec_238.0
codec_24.0 0 0 R 3.param2.decnz
codec_24.0 1 1 R codec_18.0
codec_240.0 0 0 R codec_235.0
codec_240.0 1 1 R codec_239.0
codec_241.0 0 0 R codec_223.0
codec_241.0 1 1 R codec_240.0
codec_242.0 0 0 R codec_222.0
codec_242.0 1 1 R codec_241.0
codec_25.0 0 0 R 3.param2.inc
codec_25.0 1 0 L 6.continue.1
codec_26.0 0 0 R 3.scratch1.decnz
codec_26.0 1 1 R codec_25.0
codec_27.0 0 0 R codec_24.0
codec_27.0 1 1 R codec_26.0
codec_28.0 0 0 R codec_16.0
codec_28.0 1 1 R codec_27.0
codec_29.0 0 0 R 3.axiomcode.decnz
codec_29.0 1 1 R codec_18.0
codec_3.0 0 0 R 3.wffstack.decnz
codec_3.0 1 1 R codec_2.0
codec_30.0 0 0 R 3.axiomcode.inc
codec_30.0 1 0 L 6.continue.1
codec_31.0 0 0 R 3.scratch1.decnz
codec_31.0 1 1 R codec_30.0
codec_32.0 0 0 R codec_29.0
codec_32.0 1 1 R codec_31.0
codec_33.0 0 0 R codec_16.0
codec_33.0 1 1 R codec_32.0
codec_34.0 0 0 R codec_16.0
codec_34.0 1 1 R 3.topwff.inc
codec_35.0 0 0 R codec_34.0
codec_35.0 1 1 R 3.topwff.inc
codec_36.0 0 0 R codec_35.0
codec_36.0 1 1 R 3.topwff.inc
codec_37.0 0 0 R codec_23.0
codec_37.0 1 1 R codec_28.0
codec_38.0 0 0 R 3.scratch1.decnz
codec_38.0 1 0 L 6.break.1
codec_39.0 0 0 R 3.scratch2.decnz
codec_39.0 1 1 R codec_0.0
codec_4.0 0 0 R 3.scratch1.inc
codec_4.0 1 1 R 3.scratch2.inc
codec_40.0 0 0 R codec_38.0
codec_40.0 1 1 R codec_39.0
codec_41.0 0 0 R 3.scratch2.inc
codec_41.0 1 1 R codec_40.0
codec_42.0 0 0 R codec_41.0
codec_42.0 1 0 L 6.continue.1
codec_43.0 0 0 R 3.wffstack.decnz
codec_43.0 1 1 R codec_42.0
codec_44.0 0 0 R codec_43.0
codec_44.0 1 1 R codec_13.0
codec_45.0 0 0 R 3.topwff.inc
codec_45.0 1 1 R 3.topwff.inc
codec_46.0 0 0 R codec_45.0
codec_46.0 1 1 R 3.topwff.inc
codec_47.0 0 0 R codec_46.0
codec_47.0 1 1 R 3.topwff.inc
codec_48.0 0 0 R codec_47.0
codec_48.0 1 0 L 6.continue.1
codec_49.0 0 0 R 3.scratch2.decnz
codec_49.0 1 1 R codec_48.0
codec_5.0 0 0 R codec_4.0
codec_5.0 1 0 L 6.continue.1
codec_50.0 0 0 R codec_11.0
codec_50.0 1 1 R codec_49.0
codec_51.0 0 0 R codec_44.0
codec_51.0 1 1 R codec_50.0
codec_52.0 0 0 R codec_51.0
codec_52.0 1 1 R codec_45.0
codec_53.0 0 0 R codec_37.0
codec_53.0 1 1 R codec_52.0
codec_54.0 0 0 R 3.prooflist.decnz
codec_54.0 1 1 R codec_42.0
codec_55.0 0 0 R 3.prooflist.inc
codec_55.0 1 0 L 6.continue.1
codec_56.0 0 0 R 3.scratch2.decnz
codec_56.0 1 1 R codec_55.0
codec_57.0 0 0 R codec_54.0
codec_57.0 1 1 R codec_56.0
codec_58.0 0 0 R codec_57.0
codec_58.0 1 1 R codec_26.0
codec_59.0 0 0 R codec_23.0
codec_59.0 1 1 R codec_33.0
codec_6.0 0 0 R 3.topwff.decnz
codec_6.0 1 1 R codec_5.0
codec_60.0 0 0 R codec_33.0
codec_60.0 1 1 R codec_51.0
codec_61.0 0 0 R codec_33.0
codec_61.0 1 1 R codec_23.0
codec_62.0 0 0 R codec_51.0
codec_62.0 1 1 R codec_46.0
codec_63.0 0 0 R codec_33.0
codec_63.0 1 1 R codec_28.0
codec_64.0 0 0 R codec_62.0
codec_64.0 1 1 R codec_63.0
codec_65.0 0 0 R codec_61.0
codec_65.0 1 1 R codec_64.0
codec_66.0 0 0 R codec_51.0
codec_66.0 1 1 R codec_65.0
codec_67.0 0 0 R codec_23.0
codec_67.0 1 1 R codec_37.0
codec_68.0 0 0 R codec_51.0
codec_68.0 1 1 R codec_67.0
codec_69.0 0 0 R codec_51.0
codec_69.0 1 1 R codec_68.0
codec_7.0 0 0 R 3.scratch1.decnz
codec_7.0 1 1 R codec_2.0
codec_70.0 0 0 R codec_34.0
codec_70.0 1 1 R codec_51.0
codec_71.0 0 0 R codec_52.0
codec_71.0 1 1 R codec_70.0
codec_72.0 0 0 R codec_70.0
codec_72.0 1 1 R codec_71.0
codec_73.0 0 0 R codec_72.0
codec_73.0 1 1 R codec_28.0
codec_74.0 0 0 R codec_51.0
codec_74.0 1 1 R 3.topwff.inc
codec_75.0 0 0 R codec_28.0
codec_75.0 1 1 R codec_74.0
codec_76.0 0 0 R codec_51.0
codec_76.0 1 1 R codec_37.0
codec_77.0 0 0 R codec_76.0
codec_77.0 1 1 R codec_33.0
codec_78.0 0 0 R codec_51.0
codec_78.0 1 1 R codec_77.0
codec_79.0 0 0 R codec_75.0
codec_79.0 1 1 R codec_78.0
codec_8.0 0 0 R 3.scratch2.inc
codec_8.0 1 1 R codec_7.0
codec_80.0 0 0 R codec_59.0
codec_80.0 1 1 R codec_52.0
codec_81.0 0 0 R codec_62.0
codec_81.0 1 1 R codec_61.0
codec_82.0 0 0 R codec_76.0
codec_82.0 1 1 R codec_81.0
codec_83.0 0 0 R codec_52.0
codec_83.0 1 1 R codec_82.0
codec_84.0 0 0 R codec_74.0
codec_84.0 1 1 R codec_33.0
codec_85.0 0 0 R codec_51.0
codec_85.0 1 1 R codec_52.0
codec_86.0 0 0 R codec_74.0
codec_86.0 1 1 R codec_85.0
codec_87.0 0 0 R codec_51.0
codec_87.0 1 1 R codec_70.0
codec_88.0 0 0 R codec_70.0
codec_88.0 1 1 R codec_87.0
codec_89.0 0 0 R codec_88.0
codec_89.0 1 1 R codec_72.0
codec_9.0 0 0 R codec_8.0
codec_9.0 1 0 L 6.continue.2
codec_90.0 0 0 R codec_67.0
codec_90.0 1 1 R codec_74.0
codec_91.0 0 0 R codec_63.0
codec_91.0 1 1 R codec_33.0
codec_92.0 0 0 R codec_28.0
codec_92.0 1 1 R codec_91.0
codec_93.0 0 0 R codec_33.0
codec_93.0 1 1 R codec_74.0
codec_94.0 0 0 R codec_28.0
codec_94.0 1 1 R codec_93.0
codec_95.0 0 0 R codec_72.0
codec_95.0 1 1 R codec_85.0
codec_96.0 0 0 R codec_84.0
codec_96.0 1 1 R codec_23.0
codec_97.0 0 0 R codec_28.0
codec_97.0 1 1 R codec_96.0
codec_98.0 0 0 R codec_28.0
codec_98.0 1 1 R codec_62.0
codec_99.0 0 0 R 3.axiomcode.decnz
codec_99.0 1 1 R codec_5.0
main().0 0 0 R codec_221.0
main().0 1 1 R codec_242.0
