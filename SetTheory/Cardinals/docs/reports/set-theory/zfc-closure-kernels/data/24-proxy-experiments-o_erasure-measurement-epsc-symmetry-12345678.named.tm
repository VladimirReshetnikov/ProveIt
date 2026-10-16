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
4.dispatch.7 0 0 L 4.dispatch.8
4.dispatch.7 1 1 L 6.continue.0
4.dispatch.8 0 0 L 4.dispatch.9
4.dispatch.8 1 1 L 6.continue.0
4.dispatch.9 0 0 R 5.root
4.dispatch.9 1 1 L 6.continue.0
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
axioms().74 0 0 R while_decnz(param1,3.param2.inc).0
axioms().74 1 1 R if_eq(scratch1,param2,77).0
axioms().n_100.0 0 0 R axioms().n_121.0
axioms().n_100.0 1 1 R wal().0
axioms().n_112.0 0 0 R par3().0
axioms().n_112.0 1 1 R fn_45().0
axioms().n_115.0 0 0 R fn_45().0
axioms().n_115.0 1 1 R wal().0
axioms().n_121.0 0 0 R par1().0
axioms().n_121.0 1 1 R fn_59().0
fn_14().0 0 0 R 3.prooflist.decnz
fn_14().0 1 1 R node_013.0
fn_41().0 0 0 R 3.wffstack.decnz
fn_41().0 1 1 R node_013.0
fn_44().0 0 0 R 3.scratch2.decnz
fn_44().0 1 1 R fn_44().1
fn_44().1 0 0 R node_099.0
fn_44().1 1 0 L 6.continue.1
fn_45().0 0 0 R node_110.0
fn_45().0 1 1 R fn_45().1
fn_45().1 0 0 R pair(scratch2,scratch1,topwff).0
fn_45().1 1 1 R fn_44().0
fn_59().0 0 0 R pushwff().0
fn_59().0 1 1 R fn_59().1
fn_59().1 0 0 R while_decnz(param2,37).0
fn_59().1 1 1 R while_decnz(scratch1,3.param2.inc).0
if_eq().n_055.0 0 0 R if_eq().n_055.0.0
if_eq().n_055.0 1 1 R if_eq().n_055.1
if_eq().n_055.0.0 0 0 R 3.scratch1.decnz
if_eq().n_055.0.0 1 1 R if_eq().n_055.0.1
if_eq().n_055.0.1 0 0 R if_eq().n_055.0.1.0
if_eq().n_055.0.1 1 1 R if_eq().n_055.0.2
if_eq().n_055.0.1.0 0 0 R 3.param2.decnz
if_eq().n_055.0.1.0 1 0 L 6.continue.1
if_eq().n_055.0.2 0 0 R while_decnz(scratch1,3.param2.inc).0
if_eq().n_055.0.2 1 1 R 3.param2.inc
if_eq().n_055.1 0 0 R 3.param2.decnz
if_eq().n_055.1 1 1 R if_eq().n_055.2
if_eq().n_055.2 0 0 R while_decnz(param2,()).0
if_eq().n_055.2 1 0 L 6.break.1
if_eq(scratch1,param2,40).0 0 0 R if_eq().n_055.0
if_eq(scratch1,param2,40).0 1 1 R par1().0
if_eq(scratch1,param2,77).0 0 0 R if_eq().n_055.0
if_eq(scratch1,param2,77).0 1 1 R while_decnz(topwff,()).0
if_eq(scratch1,param2,halt).0 0 0 R if_eq().n_055.0
if_eq(scratch1,param2,halt).0 1 1 R halt
if_not_decnz(prooflist,5).0 0 0 R if_not_decnz(prooflist,5).0.0
if_not_decnz(prooflist,5).0 1 1 R if_not_decnz(prooflist,5).1
if_not_decnz(prooflist,5).0.0 0 0 R 3.prooflist.decnz
if_not_decnz(prooflist,5).0.0 1 0 L 6.break.1
if_not_decnz(prooflist,5).1 0 0 R while_decnz(nextproof,0).0
if_not_decnz(prooflist,5).1 1 1 R if_not_decnz(prooflist,5).2
if_not_decnz(prooflist,5).2 0 0 R while_decnz(scratch1,3.nextproof.inc).0
if_not_decnz(prooflist,5).2 1 1 R 3.nextproof.inc
if_not_decnz(scratch1,9).0 0 0 R if_not_decnz(scratch1,9).0.0
if_not_decnz(scratch1,9).0 1 1 R while_decnz(scratch2,3.scratch1.inc).0
if_not_decnz(scratch1,9).0.0 0 0 R 3.scratch1.decnz
if_not_decnz(scratch1,9).0.0 1 0 L 6.break.1
main().0 0 0 R if_not_decnz(prooflist,5).0
main().0 1 1 R main().1
main().1 0 0 R read(axiomcode).0
main().1 1 1 R main().2
main().2 0 0 R read(param1).0
main().2 1 1 R main().3
main().3 0 0 R main().3.0
main().3 1 1 R mp().0
main().3.0 0 0 R 3.axiomcode.decnz
main().3.0 1 1 R main().3.1
main().3.1 0 0 R main().3.1.0
main().3.1 1 0 L 6.break.1
main().3.1.0 0 0 R main().3.1.0.0
main().3.1.0 1 1 R fn_59().0
main().3.1.0.0 0 0 R 3.axiomcode.decnz
main().3.1.0.0 1 1 R main().3.1.0.1
main().3.1.0.1 0 0 R main().3.1.0.1.0
main().3.1.0.1 1 0 L 6.break.1
main().3.1.0.1.0 0 0 R main().3.1.0.1.0.0
main().3.1.0.1.0 1 1 R nip().0
main().3.1.0.1.0.0 0 0 R 3.axiomcode.decnz
main().3.1.0.1.0.0 1 1 R main().3.1.0.1.0.1
main().3.1.0.1.0.1 0 0 R old_rho6_repair_3_4().0
main().3.1.0.1.0.1 1 0 L 6.break.1
mp().0 0 0 R node_111.0
mp().0 1 1 R mp().1
mp().1 0 0 R while_decnz(topwff,3.scratch1.inc).0
mp().1 1 1 R if_eq(scratch1,param2,40).0
nip().0 0 0 R 3.scratch1.inc
nip().0 1 1 R nip().1
nip().1 0 0 R if_eq(scratch1,param2,halt).0
nip().1 1 1 R pop(param2).0
node_013.0 0 0 R node_013.0.0
node_013.0 1 0 L 6.continue.1
node_013.0.0 0 0 R 3.scratch2.inc
node_013.0.0 1 1 R if_not_decnz(scratch1,9).0
node_099.0 0 0 R node_109.0
node_099.0 1 1 R 3.topwff.inc
node_108.0 0 0 R fn_14().0
node_108.0 1 1 R while_decnz(scratch2,3.prooflist.inc).0
node_109.0 0 0 R 3.topwff.inc
node_109.0 1 1 R 3.topwff.inc
node_110.0 0 0 R fn_41().0
node_110.0 1 1 R while_decnz(scratch2,3.wffstack.inc).0
node_111.0 0 0 R par1().0
node_111.0 1 1 R fn_45().0
old_rho6_repair_3_4().0 0 0 R axioms().n_100.0
old_rho6_repair_3_4().0 1 1 R old_rho6_repair_3_4().1
old_rho6_repair_3_4().1 0 0 R read(param2).0
old_rho6_repair_3_4().1 1 1 R old_rho6_repair_3_4().2
old_rho6_repair_3_4().2 0 0 R par3().0
old_rho6_repair_3_4().2 1 1 R old_rho6_repair_3_4().3
old_rho6_repair_3_4().3 0 0 R pushwff().0
old_rho6_repair_3_4().3 1 1 R old_rho6_repair_3_4().4
old_rho6_repair_3_4().4 0 0 R node_108.0
old_rho6_repair_3_4().4 1 1 R old_rho6_repair_3_4().5
old_rho6_repair_3_4().5 0 0 R while_decnz(scratch1,3.topwff.inc).0
old_rho6_repair_3_4().5 1 1 R old_rho6_repair_3_4().6
old_rho6_repair_3_4().6 0 0 R old_rho6_repair_3_4().n_223.0
old_rho6_repair_3_4().6 1 1 R old_rho6_repair_3_4().7
old_rho6_repair_3_4().7 0 0 R old_rho6_repair_3_4().n_223.0
old_rho6_repair_3_4().7 1 1 R old_rho6_repair_3_4().8
old_rho6_repair_3_4().8 0 0 R axioms().n_112.0
old_rho6_repair_3_4().8 1 1 R old_rho6_repair_3_4().9
old_rho6_repair_3_4().9 0 0 R fn_59().0
old_rho6_repair_3_4().9 1 1 R old_rho6_repair_3_4().10
old_rho6_repair_3_4().10 0 0 R axioms().n_112.0
old_rho6_repair_3_4().10 1 1 R old_rho6_repair_3_4().11
old_rho6_repair_3_4().11 0 0 R fn_45().0
old_rho6_repair_3_4().11 1 1 R old_rho6_repair_3_4().12
old_rho6_repair_3_4().12 0 0 R old_rho6_repair_3_4().n_240.0
old_rho6_repair_3_4().12 1 1 R old_rho6_repair_3_4().13
old_rho6_repair_3_4().13 0 0 R pushwff().0
old_rho6_repair_3_4().13 1 1 R old_rho6_repair_3_4().14
old_rho6_repair_3_4().14 0 0 R old_rho6_repair_3_4().n_226.0
old_rho6_repair_3_4().14 1 1 R old_rho6_repair_3_4().15
old_rho6_repair_3_4().15 0 0 R old_rho6_repair_3_4().n_249.0
old_rho6_repair_3_4().15 1 1 R old_rho6_repair_3_4().16
old_rho6_repair_3_4().16 0 0 R old_rho6_repair_3_4().n_223.0
old_rho6_repair_3_4().16 1 1 R old_rho6_repair_3_4().17
old_rho6_repair_3_4().17 0 0 R axioms().n_100.0
old_rho6_repair_3_4().17 1 1 R old_rho6_repair_3_4().18
old_rho6_repair_3_4().18 0 0 R wex().0
old_rho6_repair_3_4().18 1 1 R old_rho6_repair_3_4().19
old_rho6_repair_3_4().19 0 0 R fn_59().0
old_rho6_repair_3_4().19 1 1 R old_rho6_repair_3_4().20
old_rho6_repair_3_4().20 0 0 R old_rho6_repair_3_4().n_232.0
old_rho6_repair_3_4().20 1 1 R old_rho6_repair_3_4().21
old_rho6_repair_3_4().21 0 0 R par3().0
old_rho6_repair_3_4().21 1 1 R old_rho6_repair_3_4().22
old_rho6_repair_3_4().22 0 0 R old_rho6_repair_3_4().n_220.0
old_rho6_repair_3_4().22 1 1 R old_rho6_repair_3_4().23
old_rho6_repair_3_4().23 0 0 R old_rho6_repair_3_4().n_249.0
old_rho6_repair_3_4().23 1 1 R old_rho6_repair_3_4().24
old_rho6_repair_3_4().24 0 0 R old_rho6_repair_3_4().n_247.0
old_rho6_repair_3_4().24 1 1 R old_rho6_repair_3_4().25
old_rho6_repair_3_4().25 0 0 R old_rho6_repair_3_4().n_239.0
old_rho6_repair_3_4().25 1 1 R old_rho6_repair_3_4().26
old_rho6_repair_3_4().26 0 0 R old_rho6_repair_3_4().n_248.0
old_rho6_repair_3_4().26 1 1 R old_rho6_repair_3_4().27
old_rho6_repair_3_4().27 0 0 R old_rho6_repair_3_4().n_231.0
old_rho6_repair_3_4().27 1 1 R old_rho6_repair_3_4().28
old_rho6_repair_3_4().28 0 0 R wal().0
old_rho6_repair_3_4().28 1 1 R old_rho6_repair_3_4().29
old_rho6_repair_3_4().29 0 0 R fn_59().0
old_rho6_repair_3_4().29 1 1 R old_rho6_repair_3_4().30
old_rho6_repair_3_4().30 0 0 R old_rho6_repair_3_4().n_236.0
old_rho6_repair_3_4().30 1 1 R old_rho6_repair_3_4().31
old_rho6_repair_3_4().31 0 0 R old_rho6_repair_3_4().n_242.0
old_rho6_repair_3_4().31 1 1 R old_rho6_repair_3_4().32
old_rho6_repair_3_4().32 0 0 R old_rho6_repair_3_4().n_222.0
old_rho6_repair_3_4().32 1 1 R old_rho6_repair_3_4().33
old_rho6_repair_3_4().33 0 0 R par1().0
old_rho6_repair_3_4().33 1 1 R old_rho6_repair_3_4().34
old_rho6_repair_3_4().34 0 0 R old_rho6_repair_3_4().n_221.0
old_rho6_repair_3_4().34 1 1 R old_rho6_repair_3_4().35
old_rho6_repair_3_4().35 0 0 R old_rho6_repair_3_4().n_247.0
old_rho6_repair_3_4().35 1 1 R old_rho6_repair_3_4().36
old_rho6_repair_3_4().36 0 0 R old_rho6_repair_3_4().n_248.0
old_rho6_repair_3_4().36 1 1 R old_rho6_repair_3_4().37
old_rho6_repair_3_4().37 0 0 R par3().0
old_rho6_repair_3_4().37 1 1 R old_rho6_repair_3_4().38
old_rho6_repair_3_4().38 0 0 R axioms().n_115.0
old_rho6_repair_3_4().38 1 1 R old_rho6_repair_3_4().39
old_rho6_repair_3_4().39 0 0 R axioms().n_100.0
old_rho6_repair_3_4().39 1 1 R old_rho6_repair_3_4().40
old_rho6_repair_3_4().40 0 0 R old_rho6_repair_3_4().n_236.0
old_rho6_repair_3_4().40 1 1 R old_rho6_repair_3_4().41
old_rho6_repair_3_4().41 0 0 R old_rho6_repair_3_4().n_233.0
old_rho6_repair_3_4().41 1 1 R old_rho6_repair_3_4().42
old_rho6_repair_3_4().42 0 0 R old_rho6_repair_3_4().n_245.0
old_rho6_repair_3_4().42 1 1 R old_rho6_repair_3_4().43
old_rho6_repair_3_4().43 0 0 R old_rho6_repair_3_4().n_238.0
old_rho6_repair_3_4().43 1 1 R old_rho6_repair_3_4().44
old_rho6_repair_3_4().44 0 0 R old_rho6_repair_3_4().n_246.0
old_rho6_repair_3_4().44 1 1 R old_rho6_repair_3_4().45
old_rho6_repair_3_4().45 0 0 R old_rho6_repair_3_4().n_243.0
old_rho6_repair_3_4().45 1 1 R old_rho6_repair_3_4().46
old_rho6_repair_3_4().46 0 0 R old_rho6_repair_3_4().46.0
old_rho6_repair_3_4().46 1 1 R old_rho6_repair_3_4().47
old_rho6_repair_3_4().46.0 0 0 R v_1().0
old_rho6_repair_3_4().46.0 1 1 R v_1().0
old_rho6_repair_3_4().47 0 0 R v_1().0
old_rho6_repair_3_4().47 1 1 R old_rho6_repair_3_4().48
old_rho6_repair_3_4().48 0 0 R old_rho6_repair_3_4().n_221.0
old_rho6_repair_3_4().48 1 1 R old_rho6_repair_3_4().49
old_rho6_repair_3_4().49 0 0 R v_1().0
old_rho6_repair_3_4().49 1 1 R old_rho6_repair_3_4().50
old_rho6_repair_3_4().50 0 0 R old_rho6_repair_3_4().n_244.0
old_rho6_repair_3_4().50 1 1 R old_rho6_repair_3_4().51
old_rho6_repair_3_4().51 0 0 R wex().0
old_rho6_repair_3_4().51 1 1 R old_rho6_repair_3_4().52
old_rho6_repair_3_4().52 0 0 R wal().0
old_rho6_repair_3_4().52 1 1 R old_rho6_repair_3_4().53
old_rho6_repair_3_4().53 0 0 R old_rho6_repair_3_4().n_246.0
old_rho6_repair_3_4().53 1 1 R old_rho6_repair_3_4().54
old_rho6_repair_3_4().54 0 0 R v_1().0
old_rho6_repair_3_4().54 1 1 R old_rho6_repair_3_4().55
old_rho6_repair_3_4().55 0 0 R old_rho6_repair_3_4().n_227.0
old_rho6_repair_3_4().55 1 1 R old_rho6_repair_3_4().56
old_rho6_repair_3_4().56 0 0 R v_1().0
old_rho6_repair_3_4().56 1 1 R old_rho6_repair_3_4().57
old_rho6_repair_3_4().57 0 0 R wel().0
old_rho6_repair_3_4().57 1 1 R old_rho6_repair_3_4().58
old_rho6_repair_3_4().58 0 0 R old_rho6_repair_3_4().n_238.0
old_rho6_repair_3_4().58 1 1 R old_rho6_repair_3_4().59
old_rho6_repair_3_4().59 0 0 R old_rho6_repair_3_4().n_234.0
old_rho6_repair_3_4().59 1 1 R old_rho6_repair_3_4().60
old_rho6_repair_3_4().60 0 0 R fn_45().0
old_rho6_repair_3_4().60 1 1 R old_rho6_repair_3_4().61
old_rho6_repair_3_4().61 0 0 R old_rho6_repair_3_4().n_243.0
old_rho6_repair_3_4().61 1 1 R old_rho6_repair_3_4().62
old_rho6_repair_3_4().62 0 0 R old_rho6_repair_3_4().n_224.0
old_rho6_repair_3_4().62 1 1 R old_rho6_repair_3_4().63
old_rho6_repair_3_4().63 0 0 R old_rho6_repair_3_4().n_244.0
old_rho6_repair_3_4().63 1 1 R old_rho6_repair_3_4().64
old_rho6_repair_3_4().64 0 0 R old_rho6_repair_3_4().n_227.0
old_rho6_repair_3_4().64 1 1 R old_rho6_repair_3_4().65
old_rho6_repair_3_4().65 0 0 R old_rho6_repair_3_4().n_234.0
old_rho6_repair_3_4().65 1 1 R old_rho6_repair_3_4().66
old_rho6_repair_3_4().66 0 0 R v_1().0
old_rho6_repair_3_4().66 1 1 R old_rho6_repair_3_4().67
old_rho6_repair_3_4().67 0 0 R par3().0
old_rho6_repair_3_4().67 1 1 R old_rho6_repair_3_4().68
old_rho6_repair_3_4().68 0 0 R wex().0
old_rho6_repair_3_4().68 1 1 R old_rho6_repair_3_4().69
old_rho6_repair_3_4().69 0 0 R axioms().n_115.0
old_rho6_repair_3_4().69 1 1 R old_rho6_repair_3_4().70
old_rho6_repair_3_4().70 0 0 R wa().0
old_rho6_repair_3_4().70 1 1 R old_rho6_repair_3_4().71
old_rho6_repair_3_4().71 0 0 R wex().0
old_rho6_repair_3_4().71 1 1 R old_rho6_repair_3_4().72
old_rho6_repair_3_4().72 0 0 R old_rho6_repair_3_4().n_223.0
old_rho6_repair_3_4().72 1 1 R old_rho6_repair_3_4().73
old_rho6_repair_3_4().73 0 0 R old_rho6_repair_3_4().n_237.0
old_rho6_repair_3_4().73 1 1 R old_rho6_repair_3_4().74
old_rho6_repair_3_4().74 0 0 R old_rho6_repair_3_4().n_222.0
old_rho6_repair_3_4().74 1 1 R old_rho6_repair_3_4().75
old_rho6_repair_3_4().75 0 0 R old_rho6_repair_3_4().n_239.0
old_rho6_repair_3_4().75 1 1 R old_rho6_repair_3_4().76
old_rho6_repair_3_4().76 0 0 R old_rho6_repair_3_4().n_242.0
old_rho6_repair_3_4().76 1 1 R old_rho6_repair_3_4().77
old_rho6_repair_3_4().77 0 0 R par3().0
old_rho6_repair_3_4().77 1 1 R old_rho6_repair_3_4().78
old_rho6_repair_3_4().78 0 0 R old_rho6_repair_3_4().n_245.0
old_rho6_repair_3_4().78 1 1 R old_rho6_repair_3_4().79
old_rho6_repair_3_4().79 0 0 R wal().0
old_rho6_repair_3_4().79 1 1 R old_rho6_repair_3_4().80
old_rho6_repair_3_4().80 0 0 R fn_45().0
old_rho6_repair_3_4().80 1 1 R old_rho6_repair_3_4().81
old_rho6_repair_3_4().81 0 0 R wa().0
old_rho6_repair_3_4().81 1 1 R old_rho6_repair_3_4().82
old_rho6_repair_3_4().82 0 0 R while_decnz(axiomcode,26).0
old_rho6_repair_3_4().82 1 1 R old_rho6_repair_3_4().83
old_rho6_repair_3_4().83 0 0 R if_eq(scratch1,param2,77).0
old_rho6_repair_3_4().83 1 1 R old_rho6_repair_3_4().84
old_rho6_repair_3_4().84 0 0 R while_decnz(scratch2,3.scratch1.inc).0
old_rho6_repair_3_4().84 1 1 R axioms().74
old_rho6_repair_3_4().n_219.0 0 0 R 3.topwff.inc
old_rho6_repair_3_4().n_219.0 1 1 R pushwff().0
old_rho6_repair_3_4().n_220.0 0 0 R old_rho6_repair_3_4().n_219.0
old_rho6_repair_3_4().n_220.0 1 1 R wel().0
old_rho6_repair_3_4().n_221.0 0 0 R 3.topwff.inc
old_rho6_repair_3_4().n_221.0 1 1 R wel().0
old_rho6_repair_3_4().n_222.0 0 0 R par3().0
old_rho6_repair_3_4().n_222.0 1 1 R 3.topwff.inc
old_rho6_repair_3_4().n_223.0 0 0 R fn_45().0
old_rho6_repair_3_4().n_223.0 1 1 R par1().0
old_rho6_repair_3_4().n_224.0 0 0 R v_1().0
old_rho6_repair_3_4().n_224.0 1 1 R 3.topwff.inc
old_rho6_repair_3_4().n_225.0 0 0 R par1().0
old_rho6_repair_3_4().n_225.0 1 1 R old_rho6_repair_3_4().n_220.0
old_rho6_repair_3_4().n_226.0 0 0 R fn_59().0
old_rho6_repair_3_4().n_226.0 1 1 R old_rho6_repair_3_4().n_220.0
old_rho6_repair_3_4().n_227.0 0 0 R old_rho6_repair_3_4().n_224.0
old_rho6_repair_3_4().n_227.0 1 1 R old_rho6_repair_3_4().n_224.0
old_rho6_repair_3_4().n_228.0 0 0 R fn_59().0
old_rho6_repair_3_4().n_228.0 1 1 R old_rho6_repair_3_4().n_221.0
old_rho6_repair_3_4().n_229.0 0 0 R old_rho6_repair_3_4().n_222.0
old_rho6_repair_3_4().n_229.0 1 1 R 3.topwff.inc
old_rho6_repair_3_4().n_230.0 0 0 R old_rho6_repair_3_4().n_226.0
old_rho6_repair_3_4().n_230.0 1 1 R axioms().n_115.0
old_rho6_repair_3_4().n_231.0 0 0 R par3().0
old_rho6_repair_3_4().n_231.0 1 1 R wal().0
old_rho6_repair_3_4().n_232.0 0 0 R fn_45().0
old_rho6_repair_3_4().n_232.0 1 1 R pushwff().0
old_rho6_repair_3_4().n_233.0 0 0 R fn_45().0
old_rho6_repair_3_4().n_233.0 1 1 R old_rho6_repair_3_4().n_223.0
old_rho6_repair_3_4().n_234.0 0 0 R old_rho6_repair_3_4().n_229.0
old_rho6_repair_3_4().n_234.0 1 1 R old_rho6_repair_3_4().n_221.0
old_rho6_repair_3_4().n_235.0 0 0 R old_rho6_repair_3_4().n_225.0
old_rho6_repair_3_4().n_235.0 1 1 R old_rho6_repair_3_4().n_230.0
old_rho6_repair_3_4().n_236.0 0 0 R par1().0
old_rho6_repair_3_4().n_236.0 1 1 R old_rho6_repair_3_4().n_231.0
old_rho6_repair_3_4().n_237.0 0 0 R 3.topwff.inc
old_rho6_repair_3_4().n_237.0 1 1 R old_rho6_repair_3_4().n_228.0
old_rho6_repair_3_4().n_238.0 0 0 R wex().0
old_rho6_repair_3_4().n_238.0 1 1 R v_1().0
old_rho6_repair_3_4().n_239.0 0 0 R par1().0
old_rho6_repair_3_4().n_239.0 1 1 R old_rho6_repair_3_4().n_237.0
old_rho6_repair_3_4().n_240.0 0 0 R old_rho6_repair_3_4().n_232.0
old_rho6_repair_3_4().n_240.0 1 1 R old_rho6_repair_3_4().n_235.0
old_rho6_repair_3_4().n_242.0 0 0 R wal().0
old_rho6_repair_3_4().n_242.0 1 1 R old_rho6_repair_3_4().n_240.0
old_rho6_repair_3_4().n_243.0 0 0 R old_rho6_repair_3_4().n_224.0
old_rho6_repair_3_4().n_243.0 1 1 R par3().0
old_rho6_repair_3_4().n_244.0 0 0 R old_rho6_repair_3_4().n_244.0.0
old_rho6_repair_3_4().n_244.0 1 1 R axioms().n_115.0
old_rho6_repair_3_4().n_244.0.0 0 0 R old_rho6_repair_3_4().n_234.0
old_rho6_repair_3_4().n_244.0.0 1 1 R axioms().n_115.0
old_rho6_repair_3_4().n_245.0 0 0 R old_rho6_repair_3_4().n_219.0
old_rho6_repair_3_4().n_245.0 1 1 R old_rho6_repair_3_4().n_235.0
old_rho6_repair_3_4().n_246.0 0 0 R old_rho6_repair_3_4().n_229.0
old_rho6_repair_3_4().n_246.0 1 1 R 3.topwff.inc
old_rho6_repair_3_4().n_247.0 0 0 R old_rho6_repair_3_4().n_222.0
old_rho6_repair_3_4().n_247.0 1 1 R old_rho6_repair_3_4().n_228.0
old_rho6_repair_3_4().n_248.0 0 0 R old_rho6_repair_3_4().n_233.0
old_rho6_repair_3_4().n_248.0 1 1 R fn_59().0
old_rho6_repair_3_4().n_249.0 0 0 R old_rho6_repair_3_4().n_225.0
old_rho6_repair_3_4().n_249.0 1 1 R axioms().n_115.0
pair(scratch2,scratch1,topwff).0 0 0 R while_decnz(topwff,26).0
pair(scratch2,scratch1,topwff).0 1 1 R pair(scratch2,scratch1,topwff).1
pair(scratch2,scratch1,topwff).1 0 0 R 3.scratch1.decnz
pair(scratch2,scratch1,topwff).1 1 1 R pair(scratch2,scratch1,topwff).2
pair(scratch2,scratch1,topwff).2 0 0 R pair(scratch2,scratch1,topwff).2.0
pair(scratch2,scratch1,topwff).2 1 0 L 6.continue.2
pair(scratch2,scratch1,topwff).2.0 0 0 R 3.scratch2.inc
pair(scratch2,scratch1,topwff).2.0 1 1 R while_decnz(scratch1,3.topwff.inc).0
par1().0 0 0 R pushwff().0
par1().0 1 1 R par1().1
par1().1 0 0 R while_decnz(param1,37).0
par1().1 1 1 R while_decnz(scratch1,3.param1.inc).0
par3().0 0 0 R pushwff().0
par3().0 1 1 R par3().1
par3().1 0 0 R while_decnz(axiomcode,37).0
par3().1 1 1 R while_decnz(scratch1,3.axiomcode.inc).0
pop(param2).0 0 0 R node_110.0
pop(param2).0 1 1 R while_decnz(scratch1,3.param2.inc).0
pushwff().0 0 0 R while_decnz(topwff,3.scratch1.inc).0
pushwff().0 1 1 R pushwff().1
pushwff().1 0 0 R while_decnz(wffstack,3.topwff.inc).0
pushwff().1 1 1 R pushwff().2
pushwff().2 0 0 R pair(scratch2,scratch1,topwff).0
pushwff().2 1 1 R while_decnz(scratch2,3.wffstack.inc).0
read(axiomcode).0 0 0 R node_108.0
read(axiomcode).0 1 1 R while_decnz(scratch1,3.axiomcode.inc).0
read(param1).0 0 0 R node_108.0
read(param1).0 1 1 R while_decnz(scratch1,3.param1.inc).0
read(param2).0 0 0 R node_108.0
read(param2).0 1 1 R while_decnz(scratch1,3.param2.inc).0
v_1().0 0 0 R pushwff().0
v_1().0 1 1 R 3.topwff.inc
wa().0 0 0 R wn().0
wa().0 1 1 R wa().1
wa().1 0 0 R fn_45().0
wa().1 1 1 R wn().0
wal().0 0 0 R fn_45().0
wal().0 1 1 R node_109.0
wel().0 0 0 R fn_45().0
wel().0 1 1 R 3.topwff.inc
wex().0 0 0 R wn().0
wex().0 1 1 R wex().1
wex().1 0 0 R wal().0
wex().1 1 1 R wn().0
while_decnz().n_008.0 0 0 R 3.scratch1.inc
while_decnz().n_008.0 1 0 L 6.continue.1
while_decnz().n_024.0 0 0 R 3.topwff.inc
while_decnz().n_024.0 1 0 L 6.continue.1
while_decnz().n_027.0 0 0 R while_decnz().n_027.0.0
while_decnz().n_027.0 1 0 L 6.continue.1
while_decnz().n_027.0.0 0 0 R 3.scratch1.inc
while_decnz().n_027.0.0 1 1 R 3.scratch2.inc
while_decnz().n_038.0 0 0 R while_decnz().n_038.0.0
while_decnz().n_038.0 1 0 L 6.continue.1
while_decnz().n_038.0.0 0 0 R 3.scratch1.inc
while_decnz().n_038.0.0 1 1 R 3.topwff.inc
while_decnz().n_046.0 0 0 R 3.param2.inc
while_decnz().n_046.0 1 0 L 6.continue.1
while_decnz(axiomcode,26).0 0 0 R 3.axiomcode.decnz
while_decnz(axiomcode,26).0 1 1 R while_decnz().n_027.0
while_decnz(axiomcode,37).0 0 0 R 3.axiomcode.decnz
while_decnz(axiomcode,37).0 1 1 R while_decnz().n_038.0
while_decnz(nextproof,0).0 0 0 R 3.nextproof.decnz
while_decnz(nextproof,0).0 1 1 R while_decnz(nextproof,0).1
while_decnz(nextproof,0).1 0 0 R while_decnz(nextproof,0).1.0
while_decnz(nextproof,0).1 1 0 L 6.continue.1
while_decnz(nextproof,0).1.0 0 0 R 3.prooflist.inc
while_decnz(nextproof,0).1.0 1 1 R 3.scratch1.inc
while_decnz(param1,3.param2.inc).0 0 0 R 3.param1.decnz
while_decnz(param1,3.param2.inc).0 1 1 R while_decnz().n_046.0
while_decnz(param1,37).0 0 0 R 3.param1.decnz
while_decnz(param1,37).0 1 1 R while_decnz().n_038.0
while_decnz(param2,()).0 0 0 R 3.param2.decnz
while_decnz(param2,()).0 1 0 L 6.continue.0
while_decnz(param2,37).0 0 0 R 3.param2.decnz
while_decnz(param2,37).0 1 1 R while_decnz().n_038.0
while_decnz(scratch1,3.axiomcode.inc).0 0 0 R 3.scratch1.decnz
while_decnz(scratch1,3.axiomcode.inc).0 1 1 R while_decnz(scratch1,3.axiomcode.inc).1
while_decnz(scratch1,3.axiomcode.inc).1 0 0 R 3.axiomcode.inc
while_decnz(scratch1,3.axiomcode.inc).1 1 0 L 6.continue.1
while_decnz(scratch1,3.nextproof.inc).0 0 0 R 3.scratch1.decnz
while_decnz(scratch1,3.nextproof.inc).0 1 1 R while_decnz(scratch1,3.nextproof.inc).1
while_decnz(scratch1,3.nextproof.inc).1 0 0 R 3.nextproof.inc
while_decnz(scratch1,3.nextproof.inc).1 1 0 L 6.continue.1
while_decnz(scratch1,3.param1.inc).0 0 0 R 3.scratch1.decnz
while_decnz(scratch1,3.param1.inc).0 1 1 R while_decnz(scratch1,3.param1.inc).1
while_decnz(scratch1,3.param1.inc).1 0 0 R 3.param1.inc
while_decnz(scratch1,3.param1.inc).1 1 0 L 6.continue.1
while_decnz(scratch1,3.param2.inc).0 0 0 R 3.scratch1.decnz
while_decnz(scratch1,3.param2.inc).0 1 1 R while_decnz().n_046.0
while_decnz(scratch1,3.topwff.inc).0 0 0 R 3.scratch1.decnz
while_decnz(scratch1,3.topwff.inc).0 1 1 R while_decnz().n_024.0
while_decnz(scratch2,3.prooflist.inc).0 0 0 R 3.scratch2.decnz
while_decnz(scratch2,3.prooflist.inc).0 1 1 R while_decnz(scratch2,3.prooflist.inc).1
while_decnz(scratch2,3.prooflist.inc).1 0 0 R 3.prooflist.inc
while_decnz(scratch2,3.prooflist.inc).1 1 0 L 6.continue.1
while_decnz(scratch2,3.scratch1.inc).0 0 0 R 3.scratch2.decnz
while_decnz(scratch2,3.scratch1.inc).0 1 1 R while_decnz().n_008.0
while_decnz(scratch2,3.wffstack.inc).0 0 0 R 3.scratch2.decnz
while_decnz(scratch2,3.wffstack.inc).0 1 1 R while_decnz(scratch2,3.wffstack.inc).1
while_decnz(scratch2,3.wffstack.inc).1 0 0 R 3.wffstack.inc
while_decnz(scratch2,3.wffstack.inc).1 1 0 L 6.continue.1
while_decnz(topwff,()).0 0 0 R 3.topwff.decnz
while_decnz(topwff,()).0 1 0 L 6.continue.0
while_decnz(topwff,26).0 0 0 R 3.topwff.decnz
while_decnz(topwff,26).0 1 1 R while_decnz().n_027.0
while_decnz(topwff,3.scratch1.inc).0 0 0 R 3.topwff.decnz
while_decnz(topwff,3.scratch1.inc).0 1 1 R while_decnz().n_008.0
while_decnz(wffstack,3.topwff.inc).0 0 0 R 3.wffstack.decnz
while_decnz(wffstack,3.topwff.inc).0 1 1 R while_decnz().n_024.0
wn().0 0 0 R v_1().0
wn().0 1 1 R fn_45().0
