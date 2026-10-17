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
global.1 0 0 R 3.prooflist.decnz
global.1 1 0 L 6.break.1
global.2 0 0 R 3.scratch1.inc
global.2 1 0 L 6.continue.2
global.3 0 0 R 3.prooflist.inc
global.3 1 1 R global.2
global.4 0 0 R 3.nextproof.decnz
global.4 1 1 R global.3
global.5 0 0 R 3.nextproof.inc
global.5 1 0 L 6.continue.1
global.6 0 0 R 3.scratch1.decnz
global.6 1 1 R global.5
global.7 0 0 R global.6
global.7 1 1 R 3.nextproof.inc
global.8 0 0 R global.4
global.8 1 1 R global.7
global.9 0 0 R global.1
global.9 1 1 R global.8
global.10 0 0 R 3.scratch1.decnz
global.10 1 0 L 6.break.1
global.11 0 0 R 3.scratch1.inc
global.11 1 0 L 6.continue.1
global.12 0 0 R 3.scratch2.decnz
global.12 1 1 R global.11
global.13 0 0 R global.10
global.13 1 1 R global.12
global.14 0 0 R global.13
global.14 1 0 L 6.continue.2
global.15 0 0 R 3.scratch2.inc
global.15 1 1 R global.14
global.16 0 0 R 3.prooflist.decnz
global.16 1 1 R global.15
global.17 0 0 R 3.prooflist.inc
global.17 1 0 L 6.continue.1
global.18 0 0 R 3.scratch2.decnz
global.18 1 1 R global.17
global.19 0 0 R global.16
global.19 1 1 R global.18
global.20 0 0 R 3.axiomcode.inc
global.20 1 0 L 6.continue.1
global.21 0 0 R 3.scratch1.decnz
global.21 1 1 R global.20
global.22 0 0 R global.19
global.22 1 1 R global.21
global.23 0 0 R 3.param1.inc
global.23 1 0 L 6.continue.1
global.24 0 0 R 3.scratch1.decnz
global.24 1 1 R global.23
global.25 0 0 R global.19
global.25 1 1 R global.24
global.26 0 0 R 3.topwff.decnz
global.26 1 1 R global.11
global.27 0 0 R 3.topwff.inc
global.27 1 0 L 6.continue.1
global.28 0 0 R 3.wffstack.decnz
global.28 1 1 R global.27
global.29 0 0 R 3.scratch2.inc
global.29 1 1 R global.2
global.30 0 0 R 3.topwff.decnz
global.30 1 1 R global.29
global.31 0 0 R 3.scratch1.decnz
global.31 1 1 R global.27
global.32 0 0 R 3.scratch2.inc
global.32 1 1 R global.31
global.33 0 0 R global.32
global.33 1 0 L 6.continue.2
global.34 0 0 R 3.scratch1.decnz
global.34 1 1 R global.33
global.35 0 0 R global.30
global.35 1 1 R global.34
global.36 0 0 R 3.wffstack.inc
global.36 1 0 L 6.continue.1
global.37 0 0 R 3.scratch2.decnz
global.37 1 1 R global.36
global.38 0 0 R global.35
global.38 1 1 R global.37
global.39 0 0 R global.28
global.39 1 1 R global.38
global.40 0 0 R global.26
global.40 1 1 R global.39
global.41 0 0 R 3.topwff.inc
global.41 1 1 R global.2
global.42 0 0 R 3.param1.decnz
global.42 1 1 R global.41
global.43 0 0 R global.42
global.43 1 1 R global.24
global.44 0 0 R global.40
global.44 1 1 R global.43
global.45 0 0 R 3.param2.decnz
global.45 1 1 R global.41
global.46 0 0 R 3.param2.inc
global.46 1 0 L 6.continue.1
global.47 0 0 R 3.scratch1.decnz
global.47 1 1 R global.46
global.48 0 0 R global.45
global.48 1 1 R global.47
global.49 0 0 R global.40
global.49 1 1 R global.48
global.50 0 0 R global.44
global.50 1 1 R global.49
global.51 0 0 R 3.wffstack.decnz
global.51 1 1 R global.15
global.52 0 0 R global.51
global.52 1 1 R global.37
global.53 0 0 R 3.topwff.inc
global.53 1 1 R 3.topwff.inc
global.54 0 0 R global.53
global.54 1 1 R global.53
global.55 0 0 R global.54
global.55 1 0 L 6.continue.1
global.56 0 0 R 3.scratch2.decnz
global.56 1 1 R global.55
global.57 0 0 R global.35
global.57 1 1 R global.56
global.58 0 0 R global.52
global.58 1 1 R global.57
global.59 0 0 R global.58
global.59 1 1 R global.53
global.60 0 0 R global.50
global.60 1 1 R global.59
global.61 0 0 R global.19
global.61 1 1 R global.47
global.62 0 0 R 3.axiomcode.decnz
global.62 1 1 R global.41
global.63 0 0 R global.62
global.63 1 1 R global.21
global.64 0 0 R global.40
global.64 1 1 R global.63
global.65 0 0 R global.64
global.65 1 1 R global.40
global.66 0 0 R global.19
global.66 1 1 R global.31
global.67 0 0 R global.66
global.67 1 1 R global.58
global.68 0 0 R global.65
global.68 1 1 R global.67
global.69 0 0 R global.44
global.69 1 1 R global.58
global.70 0 0 R global.68
global.70 1 1 R global.69
global.71 0 0 R global.61
global.71 1 1 R global.70
global.72 0 0 R global.44
global.72 1 1 R global.64
global.73 0 0 R global.72
global.73 1 1 R global.58
global.74 0 0 R global.48
global.74 1 1 R global.64
global.75 0 0 R global.40
global.75 1 1 R global.74
global.76 0 0 R global.58
global.76 1 1 R global.58
global.77 0 0 R global.75
global.77 1 1 R global.76
global.78 0 0 R global.73
global.78 1 1 R global.77
global.79 0 0 R global.71
global.79 1 1 R global.78
global.80 0 0 R global.58
global.80 1 1 R 3.topwff.inc
global.81 0 0 R global.44
global.81 1 1 R global.80
global.82 0 0 R global.64
global.82 1 1 R global.81
global.83 0 0 R global.65
global.83 1 1 R global.48
global.84 0 0 R global.83
global.84 1 1 R global.80
global.85 0 0 R global.53
global.85 1 1 R global.84
global.86 0 0 R global.82
global.86 1 1 R global.85
global.87 0 0 R global.58
global.87 1 1 R global.86
global.88 0 0 R global.60
global.88 1 1 R 3.topwff.inc
global.89 0 0 R global.53
global.89 1 1 R global.88
global.90 0 0 R global.76
global.90 1 1 R global.44
global.91 0 0 R global.90
global.91 1 1 R global.60
global.92 0 0 R global.40
global.92 1 1 R 3.topwff.inc
global.93 0 0 R global.92
global.93 1 1 R global.58
global.94 0 0 R global.59
global.94 1 1 R global.93
global.95 0 0 R global.93
global.95 1 1 R global.94
global.96 0 0 R global.95
global.96 1 1 R global.49
global.97 0 0 R global.91
global.97 1 1 R global.96
global.98 0 0 R global.89
global.98 1 1 R global.97
global.99 0 0 R global.87
global.99 1 1 R global.98
global.100 0 0 R global.50
global.100 1 1 R global.80
global.101 0 0 R global.90
global.101 1 1 R global.75
global.102 0 0 R global.100
global.102 1 1 R global.101
global.103 0 0 R global.87
global.103 1 1 R global.102
global.104 0 0 R global.99
global.104 1 1 R global.103
global.105 0 0 R global.59
global.105 1 1 R global.58
global.106 0 0 R global.53
global.106 1 1 R global.49
global.107 0 0 R global.72
global.107 1 1 R global.59
global.108 0 0 R global.106
global.108 1 1 R global.107
global.109 0 0 R global.105
global.109 1 1 R global.88
global.110 0 0 R global.108
global.110 1 1 R global.109
global.111 0 0 R global.105
global.111 1 1 R global.110
global.112 0 0 R global.82
global.112 1 1 R global.84
global.113 0 0 R global.112
global.113 1 1 R global.101
global.114 0 0 R global.58
global.114 1 1 R global.59
global.115 0 0 R global.114
global.115 1 1 R global.60
global.116 0 0 R global.107
global.116 1 1 R global.90
global.117 0 0 R global.115
global.117 1 1 R global.116
global.118 0 0 R global.88
global.118 1 1 R global.96
global.119 0 0 R global.117
global.119 1 1 R global.118
global.120 0 0 R global.113
global.120 1 1 R global.119
global.121 0 0 R global.111
global.121 1 1 R global.120
global.122 0 0 R global.104
global.122 1 1 R global.121
global.123 0 0 R global.79
global.123 1 1 R global.122
global.124 0 0 R global.44
global.124 1 1 R global.100
global.125 0 0 R global.64
global.125 1 1 R global.75
global.126 0 0 R global.125
global.126 1 1 R global.84
global.127 0 0 R global.75
global.127 1 1 R global.80
global.128 0 0 R global.114
global.128 1 1 R global.127
global.129 0 0 R global.82
global.129 1 1 R global.128
global.130 0 0 R global.126
global.130 1 1 R global.129
global.131 0 0 R global.124
global.131 1 1 R global.130
global.132 0 0 R global.58
global.132 1 1 R global.93
global.133 0 0 R global.93
global.133 1 1 R global.132
global.134 0 0 R global.133
global.134 1 1 R global.95
global.135 0 0 R global.134
global.135 1 1 R global.64
global.136 0 0 R global.84
global.136 1 1 R global.135
global.137 0 0 R global.114
global.137 1 1 R global.136
global.138 0 0 R global.114
global.138 1 1 R global.133
global.139 0 0 R global.112
global.139 1 1 R global.138
global.140 0 0 R global.137
global.140 1 1 R global.139
global.141 0 0 R global.131
global.141 1 1 R global.140
global.142 0 0 R global.75
global.142 1 1 R global.75
global.143 0 0 R global.142
global.143 1 1 R global.127
global.144 0 0 R global.124
global.144 1 1 R global.143
global.145 0 0 R global.134
global.145 1 1 R global.114
global.146 0 0 R global.144
global.146 1 1 R global.145
global.147 0 0 R global.137
global.147 1 1 R global.146
global.148 0 0 R global.49
global.148 1 1 R global.127
global.149 0 0 R global.72
global.149 1 1 R global.95
global.150 0 0 R global.148
global.150 1 1 R global.149
global.151 0 0 R global.114
global.151 1 1 R global.150
global.152 0 0 R global.138
global.152 1 1 R global.95
global.153 0 0 R global.133
global.153 1 1 R global.100
global.154 0 0 R global.152
global.154 1 1 R global.153
global.155 0 0 R global.151
global.155 1 1 R global.154
global.156 0 0 R global.64
global.156 1 1 R global.100
global.157 0 0 R global.156
global.157 1 1 R global.109
global.158 0 0 R global.64
global.158 1 1 R global.88
global.159 0 0 R global.105
global.159 1 1 R global.133
global.160 0 0 R global.158
global.160 1 1 R global.159
global.161 0 0 R 3.axiomcode.decnz
global.161 1 1 R global.29
global.162 0 0 R global.133
global.162 1 1 R global.161
global.163 0 0 R 3.param2.decnz
global.163 1 0 L 6.continue.1
global.164 0 0 R global.47
global.164 1 1 R 3.param2.inc
global.165 0 0 R global.163
global.165 1 1 R global.164
global.166 0 0 R 3.scratch1.decnz
global.166 1 1 R global.165
global.167 0 0 R 3.param2.decnz
global.167 1 0 L 6.continue.0
global.168 0 0 R global.167
global.168 1 0 L 6.break.1
global.169 0 0 R 3.param2.decnz
global.169 1 1 R global.168
global.170 0 0 R global.166
global.170 1 1 R global.169
global.171 0 0 R 3.topwff.decnz
global.171 1 0 L 6.continue.0
global.172 0 0 R global.170
global.172 1 1 R global.171
global.173 0 0 R 3.param1.decnz
global.173 1 1 R global.46
global.174 0 0 R global.12
global.174 1 1 R global.173
global.175 0 0 R global.172
global.175 1 1 R global.174
global.176 0 0 R global.175
global.176 1 1 R global.172
global.177 0 0 R global.162
global.177 1 1 R global.176
global.178 0 0 R global.160
global.178 1 1 R global.177
global.179 0 0 R global.157
global.179 1 1 R global.178
global.180 0 0 R global.155
global.180 1 1 R global.179
global.181 0 0 R global.147
global.181 1 1 R global.180
global.182 0 0 R global.141
global.182 1 1 R global.181
global.183 0 0 R global.123
global.183 1 1 R global.182
global.184 0 0 R global.60
global.184 1 1 R global.183
global.185 0 0 R global.184
global.185 1 0 L 6.break.1
global.186 0 0 R 3.axiomcode.decnz
global.186 1 1 R global.185
global.187 0 0 R global.170
global.187 1 1 R halt
global.188 0 0 R global.52
global.188 1 1 R global.47
global.189 0 0 R global.187
global.189 1 1 R global.188
global.190 0 0 R 3.scratch1.inc
global.190 1 1 R global.189
global.191 0 0 R global.186
global.191 1 1 R global.190
global.192 0 0 R global.191
global.192 1 0 L 6.break.1
global.193 0 0 R 3.axiomcode.decnz
global.193 1 1 R global.192
global.194 0 0 R global.193
global.194 1 1 R global.49
global.195 0 0 R global.194
global.195 1 0 L 6.break.1
global.196 0 0 R 3.axiomcode.decnz
global.196 1 1 R global.195
global.197 0 0 R global.69
global.197 1 1 R global.26
global.198 0 0 R global.170
global.198 1 1 R global.44
global.199 0 0 R global.197
global.199 1 1 R global.198
global.200 0 0 R global.196
global.200 1 1 R global.199
global.201 0 0 R global.25
global.201 1 1 R global.200
global.202 0 0 R global.22
global.202 1 1 R global.201
main().0 0 0 R global.9
main().0 1 1 R global.202
