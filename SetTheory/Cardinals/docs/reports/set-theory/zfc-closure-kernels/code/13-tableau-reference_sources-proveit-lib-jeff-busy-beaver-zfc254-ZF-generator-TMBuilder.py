#!/usr/bin/python3

import tm
import tmdb
import argparse


framework = """
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
# Find end of register to decrement:
# decnz.e> [1s] 1 0
# [1s] 1 <1.decnz 0
# [1s] <1.decnz.g 1 0
1.decnz.e 1 1 R 1.decnz.e
1.decnz.e 0 0 L 1.decnz
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
1.sel.f 1 1 L 1.sel.f
1.sel.f 0 0 R 1.sel.e
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
#
# 4. dispatch
#
# Find the start of the IP. We pass by a set number of 0 cells going
# left (how many depends on the decision tree), then scan right for the
# first 1 cell.
#
4.dispatch.1 0 0 L 4.dispatch.2
4.dispatch.1 1 1 L 6.continue.0
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
"""


large_bootstrap = """
#! start 0a.boot1.A
# Based on the NQL register machine:
# <https://github.com/sorear/metamath-turing-machines>
#
# States that begin with a digit are the states for the framework of the
# register machine implemented in a turing machine. States that don't begin
# with a digit are the decision tree states from the subroutines and main().
#
# 0a. boot1
#
0a.boot1.A 0 1 L 0a.boot1.B
0a.boot1.A 1 0 R 0a.boot1.C
0a.boot1.B 0 0 L 0a.boot1.C
0a.boot1.B 1 0 L 0b.boot2.a
0a.boot1.C 0 1 L 0a.boot1.D
0a.boot1.C 1 0 L 0a.boot1.E
0a.boot1.D 0 1 R 0a.boot1.E
0a.boot1.D 1 0 L 0a.boot1.A
0a.boot1.E 0 0 R 0a.boot1.A
0a.boot1.E 1 0 R 0a.boot1.E
#
# At the end of boot1 the tape looks like:
# 100 1000^12 <a 01^132 011 01^68
#
# We can clean up the 1000s with only a couple of states leaving plenty of
# room for the IP.
#
0b.boot2.a 0 0 L 0b.boot2.b
# There are a number of states we could transition into here to start
# the main loop. We will transition into 1.add which will add one register
# to the end of the register file, because why not?
# Once the main loop starts we won't ever want to call 1.inc without at
# least 0.sel first otherwise the register numbering will change, but we
# haven't started using the registers yet here so it is okay.
0b.boot2.a 1 1 R 1.inc
0b.boot2.b 0 0 L 0b.boot2.a
0b.boot2.b 1 0 L 0b.boot2.a
"""


class Register(str):
    @property
    def inc(self):
        return "3." + self + ".inc"

    @property
    def dec(self):
        return "3." + self + ".dec"

    @property
    def decnz(self):
        return "3." + self + ".decnz"

class Sequence():
    def __init__(self, seq):
        self.seq = seq
        self.name = None
        self.unresolved_labels = set()

    def __repr__(self):
        if self.name:
            return f"{self.name}{self.seq}"
        else:
            return f"{self.seq}"

def subroutine(func):
    """Decorator which memoizes a method, and adds the return value to the sequences list"""

    def _wrapper(self, *args):
        new_args = tuple(self.add_sequence(v) for v in args)
        key = (func.__name__, *new_args)
        try:
            return self.memo[key]
        except KeyError:
            pass

        rv = tuple(v for v in (self.add_sequence(v2) for v2 in func(self, *new_args)) if v != ())
        self.memo[key] = rv
        if rv == ():
            return ()
        subroutine_seq = self.add_sequence(rv)
        if self.sequences[subroutine_seq].name is None:
            self.sequences[subroutine_seq].name = "{}({}).0".format(func.__name__, ",".join(str(v) for v in new_args))
        else:
            self.sequences[subroutine_seq].name = "fn_{}().0".format(subroutine_seq)
        return rv

    return _wrapper



class TMBuilder:
    """Subclass this class to build a particular turing machine"""
    def __init__(self):
        self.tm = tm.TuringMachine()
        self.registers = {}
        self.nextreg = 0
        self.prevreg = None
        self.sequences = []
        self.sequence_lookup = {}
        self.memo = {}
        self.debug = False

    def reg(self, name):
        if name not in self.registers:
            assert self.nextreg < 68, "The 69th register is not initialized to 0 by boot"
            reg = Register(name)
            self.tm.states[(reg.inc, "0")] = \
                tm.Transition("0", "R", "1.sel")
            self.tm.states[(reg.decnz, "0")] = \
                tm.Transition("0", "R", "1.sel")
            self.tm.states[(reg.dec, "0")] = \
                tm.Transition("0", "R", reg.decnz)
            self.tm.states[(reg.dec, "1")] = \
                tm.Transition("0", "L", "6.break.0")
            if not self.prevreg:
                self.tm.states[(reg.inc, "1")] = \
                    tm.Transition("1", "R", "1.inc")
                self.tm.states[(reg.decnz, "1")] = \
                    tm.Transition("1", "R", "1.decnz")
            else:
                self.tm.states[(reg.inc, "1")] = \
                    tm.Transition("1", "R", self.prevreg.inc)
                self.tm.states[(reg.decnz, "1")] = \
                    tm.Transition("1", "R", self.prevreg.decnz)
            self.nextreg = self.nextreg + 1
            self.registers[name] = reg
            self.prevreg = reg
        return self.registers[name]

    def add_sequence(self, tree):
        while isinstance(tree, (list, tuple)) and len(tree) == 1:
            tree=tree[0]

        if not isinstance(tree, (list, tuple)):
            return tree

        if len(tree) == 0:
            return ()

        key = tuple(v for v in (self.add_sequence(entry) for entry in tree) if v!= ())

        if len(key) == 0:
            return ()
        if len(key) == 1:
            return key[0]

        if key not in self.sequence_lookup:
            seq = Sequence(key)
            for v in key:
                if isinstance(v, int):
                    seq.unresolved_labels.update(self.sequences[v].unresolved_labels)
                elif v.startswith("break_") or v.startswith("continue_"):
                    seq.unresolved_labels.add(v.split("_", maxsplit=1)[1])

            self.sequence_lookup[key] = len(self.sequences)
            self.sequences.append(seq)

        return self.sequence_lookup[key]

    def label(self, name, seq, zeros=0, ones=0):
        control_flow = ("break_" + name, "continue_" + name)

        def contains_reference(name, seq):
            for entry in seq:
                if entry in control_flow:
                    return True
                if isinstance(entry, int) and name in self.sequences[entry].unresolved_labels:
                    return True
                if isinstance(entry, tuple) or isinstance(entry, list):
                    if contains_reference(name, entry):
                        return True
            return False

        def resolve_entry(zeros, ones, val):
            if val in control_flow:
                if val == "break_" + name:
                    return "_break.{}".format(zeros)
                else:
                    return "_continue.{}".format(ones)
            if isinstance(val, int) and name in self.sequences[val].unresolved_labels:
                rv=self.add_sequence(self.label(name, self.sequences[val].seq, zeros, ones))
                # transfer the sequence name over to the new sequence
                self.sequences[rv].name = self_sequences[val].name
                return rv
            if isinstance(val, tuple) or isinstance(val, list):
                return self.label(name, val, zeros, ones)
            return val

        if not contains_reference(name, seq):
            return seq

        if len(seq) == 2:
            return (resolve_entry(zeros + 1, ones, seq[0]),
                    resolve_entry(zeros, ones + 1, seq[1]))

        assert False, "unimplemented"

    def find_seq(self, name):
        for i in range(len(self.sequences)):
            if self.sequences[i].name == name:
                return i

    def reachable(self):
        grey = set()
        black = set()
        grey.add(self.find_seq("main().0"))

        while grey:
            i = grey.pop()
            if i not in black:
                yield i
                black.add(i)
                for v in self.sequences[i].seq:
                    if isinstance(v, int):
                        grey.add(v)

    def breakout_common_subsequences(self):

        search_len = max(len(s.seq) for s in self.sequences)

        while search_len > 1:
            subsequences = set()
            match = None
            reachable = [v for v in self.reachable()]
            for i in reachable:
                s = self.sequences[i]
                if len(s.seq) == search_len:
                    if s.seq in subsequences:
                        # we have a duplicate
                        match = s.seq
                        break
                    subsequences.add(s.seq)

            if match:
                find = max(i for i in self.reachable if self.sequences[i].seq == match)
                replace = min(i for i in self.reachable if self.sequences[i].seq == match)
                self.sequence_lookup[self.sequences[replace].seq] = replace
                for i in reachable:
                    s = self.sequences[i].seq
                    if find in s:
                        self.sequences[i].seq = tuple(v if v != find else replace for v in s)
                        self.sequence_lookup[self.sequences[i].seq] = i

                continue

            for i in reachable:
                s = self.sequences[i]
                if len(s.seq) > search_len:
                    for offset in range(len(s.seq) + 1 - search_len):
                        subseq=s.seq[offset:offset+search_len]
                        if subseq in subsequences:
                            match = subseq
                            break
                        subsequences.add(subseq)
                if match:
                    break

            if match:
                match_i = self.add_sequence(match)
                for i in reachable:
                    while True:
                        s = self.sequences[i].seq
                        if len(s) > search_len:
                            for offset in range(len(s) + 1 - search_len):
                                if s[offset:offset+search_len] == match:
                                    self.sequences[i].seq = s[0:offset] + (match_i,) + s[offset+search_len:]
                                    self.sequence_lookup[self.sequences[i].seq] = i
                                    break
                            else:
                                break
                        else:
                            break
            else:
                search_len = search_len - 1

    def reduce_to_cons(self):
        """ break all sequences down into 2-tuples"""

        i = 0
        while i < len(self.sequences):
            s = self.sequences[i].seq
            if len(s) > 2:
                cdr = self.add_sequence(s[1:])
                self.sequences[i].seq = (s[0], cdr)
            i = i + 1

    def name_sequences(self):
        """Infill node names based on branching patterns from supplied node names (from subroutine names)

        These will become state names."""

        proposed = {i: self.sequences[i].name for i in range(len(self.sequences))
                    if self.sequences[i].name is not None}
        changed = True
        while changed:
            changed = False
            for i in range(len(self.sequences)):
                try:
                    name = proposed[i]
                except KeyError:
                    continue
                for branch, node in enumerate(self.sequences[i].seq):
                    if branch == 0:
                        node_name = name + ".0"
                    else:
                        node_name = name.rsplit(".", maxsplit=1)[0] + "." + \
                            str(int(name.rsplit(".", maxsplit=1)[1]) + 1)

                    if isinstance(node, int) and self.sequences[node].name is None:
                        if node not in proposed:
                            proposed[node] = node_name
                            changed = True
                        elif node_name != proposed[node]:
                            if node_name.split("(")[0] == proposed[node].split("(")[0]:
                                # we can keep the subroutine name to provide some context
                                if ").n_" in node_name and not ").n_" in proposed[node]:
                                    proposed[node] = node_name
                                    changed = True
                                else:
                                    node_name = node_name.split("(")[0] + f"().n_{node:03}.0"
                                    if node_name != proposed[node]:
                                        proposed[node] = node_name
                                        changed = True
                            elif node_name.startswith("node_") and not proposed[node].startswith("node_"):
                                proposed[node] = node_name
                                changed = True
                            else:
                                node_name = f"node_{node:03}.0"
                                if node_name != proposed[node]:
                                    proposed[node] = node_name
                                    changed = True


        for i in proposed:
            self.sequences[i].name = proposed[i]

        #ensure all names are unique
        previous_names = set()
        dup_names = set()
        for i in self.reachable():
            if self.sequences[i].name in previous_names:
                dup_names.add(self.sequences[i].name)
            previous_names.add(self.sequences[i].name)

        for i in self.reachable():
            if self.sequences[i].name in dup_names:
                self.sequences[i].name += f".n{i:03}"

    def generate(self):

        def consecutive_zeros(v):
            if isinstance(v, int):
                s = self.sequences[v].seq
                return 1 + consecutive_zeros(s[0])
            else:
                return 0

        def generate_break(level):
            while level > 0:
                self.tm.states[(f"6.break.{level}", "0")] = \
                    tm.Transition("0", "L", f"6.break.{level - 1}")
                self.tm.states[(f"6.break.{level}", "1")] = \
                    tm.Transition("0", "L", f"6.break.{level}")
                level -= 1

        def generate_continue(level):
            while level > 0:
                self.tm.states[(f"6.continue.{level}", "0")] = \
                    tm.Transition("0", "L", f"6.continue.{level}")
                self.tm.states[(f"6.continue.{level}", "1")] = \
                    tm.Transition("0", "L", f"6.continue.{level - 1}")
                level -= 1

        max_zeros = max(consecutive_zeros(seq_i) for seq_i in self.reachable())
        max_zeros = max(max_zeros, 2)

        for lineno, l in enumerate(framework.splitlines()):
            self.tm.loadline(l, "<framework>", lineno)

        for i in range(2, max_zeros):
            self.tm.states[("4.dispatch.{}".format(i), "0")] = \
                tm.Transition("0", "L", f"4.dispatch.{i+1}")
            self.tm.states[("4.dispatch.{}".format(i), "1")] = \
                tm.Transition("1", "L", "6.continue.0")

        self.tm.states[("4.dispatch.{}".format(max_zeros), "0")] = \
            tm.Transition("0", "R", "5.root")
        self.tm.states[("4.dispatch.{}".format(max_zeros), "1")] = \
            tm.Transition("1", "L", "6.continue.0")

        # We need 6.continue.4 to exist for the boot to transition into:
        generate_continue(4)

        # the framework is now ready except for the break and continue states
        # Generate the decision tree states and the needed framework states.
        for seq_i in self.reachable():
            seq = self.sequences[seq_i]
            if isinstance(seq.seq[0], int):
                self.tm.states[(seq.name, "0")] = \
                    tm.Transition("0", "R", self.sequences[seq.seq[0]].name)
            elif seq.seq[0].startswith("_break."):
                if seq.seq[0] == "_break.0":
                    self.tm.states[(seq.name, "0")] = \
                        tm.Transition("1", "L", "6.continue.0")
                else:
                    break_i = int(seq.seq[0].split(".")[1]) - 1
                    self.tm.states[(seq.name, "0")] = \
                        tm.Transition("0", "L", f"6.break.{break_i}")
                    generate_break(break_i)
            elif seq.seq[0].startswith("_continue."):
                continue_i = int(seq.seq[0].split(".")[1])
                self.tm.states[(seq.name, "0")] = \
                    tm.Transition("0", "L", f"6.continue.{continue_i}")
                generate_continue(continue_i)
            else:
                self.tm.states[(seq.name, "0")] = \
                     tm.Transition("0", "R", seq.seq[0])

            if isinstance(seq.seq[1], int):
                self.tm.states[(seq.name, "1")] = \
                    tm.Transition("1", "R", self.sequences[seq.seq[1]].name)
            elif seq.seq[1].startswith("_break."):
                break_i = int(seq.seq[1].split(".")[1])
                self.tm.states[(seq.name, "1")] = \
                    tm.Transition("0", "L", f"6.break.{break_i}")
                generate_break(break_i)
            elif seq.seq[1].startswith("_continue."):
                continue_i = int(seq.seq[1].split(".")[1]) - 1
                assert continue_i >= 0 # otherwise we've somehow generated an infinite loop
                self.tm.states[(seq.name, "1")] = \
                    tm.Transition("0", "L", f"6.continue.{continue_i}")
                generate_continue(continue_i)
            else:
                self.tm.states[(seq.name, "1")] = \
                    tm.Transition("1", "R", seq.seq[1])

    def build_machine(self):
        self.main()
        self.breakout_common_subsequences()
        self.reduce_to_cons()
        self.name_sequences()
        self.generate()
        self.tm.gc()
        self.tm.statename = self.tm.start


    def process_cmdline(self):
        parser = argparse.ArgumentParser(description="Compiles to turing machines.")
        parser.add_argument('--debug', action='store_true',
                            help='Compile asserts')
        args = parser.parse_args()
        self.debug = args.debug

        self.build_machine()
        print("states count:")
        print("framework:    {}".format(len(set(state[0] for state in self.tm.states if state[0][0] in "0123456789"))))
        print("decision DAG: {}".format(len(set(state[0] for state in self.tm.states if state[0][0] not in "0123456789"))))
        print("total:        {}".format(len(set(state[0] for state in self.tm.states))))
        debugger = tmdb.TMDB()
        debugger.tm = self.tm
        debugger.mainloop()

    @subroutine
    def while_decnz(self, var, body):
        if body == ():
            return [
                self.label(
                "loop",
                [
                    var.decnz,
                    "continue_loop"
                ])
                   ]
        else:
            return [
                self.label(
                "loop",
                [
                    var.decnz,
                    [
                        body,
                        "continue_loop"
                    ]
                ])
                    ]

    @subroutine
    def if_decnz(self, var, body):
        assert body != ()
        return [[
            var.decnz,
            body
            ]]

    @subroutine
    def if_not_decnz(self, var, body):
        assert body != ()
        return [
            self.label(
            "fn",
            [
                [
                    var.decnz,
                    "break_fn"
                ],
                body
            ])
                ]

    @subroutine
    # zeros in1, in2
    def pair(self, out, in1, in2):
        assert out not in (in1, in2)
        return [
            self.label(
            "loop",
            [
                self.while_decnz(in1, [in2.inc, out.inc]),
                [
                    in2.decnz,
                    [
                        [
                            out.inc,
                            self.while_decnz(in2, in1.inc),
                        ],
                        "continue_loop"
                    ]
                ]
            ])
                ]


    @subroutine
    # zeros in1
    def unpair(self, out1, out2, in1):
        assert in1 not in (out1, out2)

        return [
            self.label(
            "loop",
            [
                in1.decnz,
                [
                    out1.inc,
                    [
                        [
                            out2.decnz,
                            "continue_loop"
                        ],
                        [
                            self.while_decnz(out1, out2.inc),
                            "continue_loop"
                        ]
                    ]
                ]
            ])
               ]

    @subroutine
    # zeros in1, in2
    def if_eq(self, in1, in2, body):
        return [
            self.label(
            "fn",
            [
                [
                    self.label(
                    "loop",
                    [
                        #continue
                        in1.decnz,
                        [
                            [
                                in2.decnz,
                                "continue_loop"
                            ],
                            [
                                # in1 > in2
                                # zero in1 and return
                                self.while_decnz(in1, ()),
                                "break_fn"
                            ]
                        ]
                    ]),
                    # if in2 is 0 then the two match
                    [
                        in2.decnz,
                        [
                            # in2 > in1
                            # zero in2 and return
                            self.while_decnz(in2, ()),
                            "break_fn"
                        ]
                    ],
                ],
                body
            ])
                ]

    @subroutine
    # zeros in1, in2
    def if_neq(self, in1, in2, body):
        return [
            self.label(
            "fn",
            [
                self.label(
                "test",
                [
                    self.label(
                    "loop",
                    [
                        in1.decnz,
                        [
                            [
                                in2.decnz,
                                "continue_loop"
                            ],
                            [
                                # in1 > in2
                                # zero in1 and break to body
                                self.while_decnz(in1, ()),
                                "break_test"
                            ]
                        ]
                    ]),
                    # if in2 is 0 then the two match
                    [
                        [
                            in2.decnz,
                            [
                                # in2 > in1
                                # zero in2 and break to body
                                self.while_decnz(in2, ()),
                                "break_test"
                            ]
                        ],
                        "break_fn"
                    ]
                ]),
                body
            ])
               ]

    @subroutine
    def add_value(self, var, value):
        if value < 2:
            if value == 0:
                return []
            else:
                return [ var.inc ]
        else:
            return [
                self.add_value(var, 1 << ((value - 1).bit_length() - 1)),
                self.add_value(var, value - (1 << ((value - 1).bit_length() - 1)))
                   ]

    @subroutine
    def copy(self, out1, in1):
        return [
            self.while_decnz(out1, ()),
            self.while_decnz(in1, self.reg("copy_scratch").inc),
            self.while_decnz(self.reg("copy_scratch"), [in1.inc, out1.inc])
               ]

    @subroutine
    def assert_eq(self, var1, var2):
        return [
            self.copy(self.reg("assert_var1"), var1),
            self.copy(self.reg("assert_var2"), var2),
            self.if_neq(self.reg("assert_var1"),
                        self.reg("assert_var2"),
                        f"assert_eq({var1},{var2})!failed")
               ]

    @subroutine
    def assert_eq_val(self, var1, val):
        return [
            self.copy(self.reg("assert_var1"), var1),
            self.add_value(self.reg("assert_var2"), val),
            self.if_neq(self.reg("assert_var1"),
                        self.reg("assert_var2"),
                        f"assert_eq({var1},{val})!failed")
               ]

    def debug_assert_eq(self, var1, var2):
        if self.debug:
            return self.assert_eq(var1, var2)
        else:
            return []

    def debug_assert_eq_val(self, var1, val):
        if self.debug:
            return self.assert_eq_val(var1, val)
        else:
            return []

