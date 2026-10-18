#!/usr/bin/python3

import sys
import argparse
import traceback
from tm import TuringMachine

class TMDB:

    def __init__(self):
        self.tm = TuringMachine()
        self.breakpoints = set()
        self.quit = False
        self.repeatcommand = False
        self.listsize = 10
        self.stdin_lineno = 1

    def repeatcount(self, cmd):
        if len(cmd) == 2 and cmd[1].isnumeric():
            return int(cmd[1])
        else:
            return 1

    def processcommand(self, cmd):

        self.repeatcommand = False

        if cmd.startswith("tm") and len(cmd.split()) > 1:
            if not self.tm.loadline(cmd.split(maxsplit=1)[1], "<STDIN>", self.stdin_lineno):
                print("Could not parse state")
            self.stdin_lineno = self.stdin_lineno + 1
            return False
        cmd = cmd.split()

        if cmd[0] in ("s", "step", "si"):
            for _ in range(self.repeatcount(cmd)):
                if not self.tm.step():
                    break
                if self.tm.statename in self.breakpoints or self.tm.looping:
                    break
            self.repeatcommand = True
            return True

        if cmd[0] in ("n", "next", "ni"):
            for _ in range(self.repeatcount(cmd)):
                currentname = self.tm.statename
                while self.tm.statename == currentname:
                    if not self.tm.step():
                        break
                    if self.tm.looping:
                        break
                if self.tm.statename in self.breakpoints:
                    break
            self.repeatcommand = True
            return True

        if cmd[0] in ("c", "continue"):
            for _ in range(self.repeatcount(cmd)):
                while True:
                    currentname = self.tm.statename
                    while self.tm.statename == currentname:
                        if not self.tm.step():
                            return True
                        if self.tm.looping:
                            return True
                    if self.tm.statename in self.breakpoints:
                        break
            self.repeatcommand = True
            return True

        if cmd[0] in ("start",):
            self.tm.left = []
            self.tm.right = []
            self.tm.symbol = self.tm.fill
            self.tm.statename = self.tm.start
            self.tm.stepcount = 0
            return True

        if cmd[0] in ("run",):
            self.processcommand("start")
            return self.processcommand("continue")

        if cmd[0] in ("jump",):
            if len(cmd) != 2:
                print("jump [state]")
                return False
            self.tm.statename = cmd[1]
            return True

        if cmd[0] in ("q", "quit"):
            self.quit = True
            return False

        if cmd[0] in ("load",):
            if len(cmd) != 2:
                print("load [filename]")
                return False
            self.tm.load(cmd[1])

        if cmd[0] in ("save",):
            if len(cmd) != 2:
                print("save [filename]")
                return False
            self.tm.save(cmd[1])
            return False

        if cmd[0] in ("bt", "backtrace"):
            for trace in reversed(self.tm.statetrace):
                if (trace[0], trace[1]) in self.tm.states:
                    state = self.tm.states[(trace[0], trace[1])]
                    print("{} {} x {}: {} {} {}".format(*trace, *state))
                else:
                    print("{} {} x {}".format(trace[0], trace[1], trace[2]))
            return False

        if cmd[0] in ("set",):
            if len(cmd) > 2 and cmd[1] in ("listsize") and cmd[2].isnumeric():
                self.listsize = int(cmd[2])
                return False

        if cmd[0] in ("l", "list"):
            listing = []
            filename = None
            lineno = 1
            if (self.tm.statename, self.tm.symbol) in self.tm.sourcemap:
                filename, lineno = self.tm.sourcemap[(self.tm.statename, self.tm.symbol)]
            if len(cmd) > 1:
                if ":" not in cmd[1]:
                    statename = cmd[1].split(",")[0] # range is unsupported we just use the start
                    for symbol in reversed(sorted(self.tm.symbols)):
                        if (statename, symbol) in self.tm.sourcemap:
                            filename, lineno = self.tm.sourcemap[(statename, symbol)]
                elif cmd[1].split(":")[1].isnumeric():
                    filename = cmd[1].split(":")[0]
                    lineno = cmd[1].split(":")[1]

            lines_displayed = 0
            lines = []
            for offset in range(self.listsize):
                if (filename, lineno + offset) in self.tm.source:
                    if lines_displayed == 0:
                        lines.append(">{} {}: {}".format(filename, lineno + offset, self.tm.source[(filename, lineno + offset)]))
                    else:
                        lines.append(" {} {}: {}".format(filename, lineno + offset, self.tm.source[(filename, lineno + offset)]))
                    lines_displayed = lines_displayed + 1
                if offset > 0 and (filename, lineno - offset) in self.tm.source:
                    lines.insert(0," {} {}: {}".format(filename, lineno - offset, self.tm.source[(filename, lineno - offset)]))
                    lines_displayed = lines_displayed + 1
                if lines_displayed >= self.listsize:
                    break

            if lines:
                for line in lines:
                    print(line)
            else:
                print("unable to find source")
            return False

        if cmd[0] in ("b", "break"):
            if len(cmd) == 2:
                self.breakpoints.add(cmd[1])
                for symbol in self.tm.symbols:
                    if (cmd[1], symbol) in self.tm.states:
                        break
                else:
                    print(f"warning: {cmd[1]} is not one of the tm states")
            else:
                self.breakpoints.add(self.tm.statename)
            return False

        if cmd[0] in ("clear"):
            self.breakpoints = set()
            return False

        if cmd[0] in ("info"):
            if cmd[1] in ("b", "break", "breakpoints"):
                for bp in self.breakpoints:
                    if bp in self.tm.sourcemap:
                        filename, lineno = self.tm.sourcemap[bp]
                        print("{} {}: {}".format(filename, lineno, self.tm.source[(filename, lineno)]))
                    else:
                        print(bp)
            if cmd[1] in ("registers", "tape"):
                i = -len(self.tm.left)
                current_cells = []
                while i <= len(self.tm.right):
                    # look for a run
                    for pattern_length in (1,2,3,4,5):
                        run_length = 1
                        while i + run_length*pattern_length < len(self.tm.right):
                            for pattern_i in range(pattern_length):
                                if self.tm.tape_at(i + pattern_i) != self.tm.tape_at(i + pattern_i + run_length*pattern_length):
                                    break
                            else:
                                run_length = run_length + 1
                                continue
                            break
                        if run_length >= 10:
                            break
                    else:
                        current_cells.append(self.tm.tape_at(i))
                        i = i + 1
                        continue

                    # we have found a run
                    if current_cells:
                        print("{:>10} x {}".format(1, "".join(current_cells)))

                    current_cells = []
                    for pattern_i in range(pattern_length):
                        current_cells.append(self.tm.tape_at(i + pattern_i))

                    print("{:>10} x {}".format(run_length, "".join(current_cells)))
                    current_cells = []
                    i = i + pattern_length * run_length

                if current_cells:
                    print("{:>10} x {}".format(1, "".join(current_cells)))

            return False

        return True # by default print information


    def mainloop(self):
        lastcommand = ""

        while not self.quit:
            cmd = input("(tmdb) ")
            if cmd == "" and self.repeatcommand:
                cmd = lastcommand
            lastcommand = cmd
            try:
                printstatus = self.processcommand(cmd)
            except Exception:
                traceback.print_exc()
                printstatus = True

            if printstatus:
                if len(self.tm.left) >= 35:
                    left = "".join(self.tm.left[-35:])
                else:
                    left = (("0" * 35) + "".join(self.tm.left))[-35:]
                if len(self.tm.right) >= 35:
                    right = "".join(reversed(self.tm.right[-35:]))
                else:
                    right = ("".join(reversed(self.tm.right)) + ("0" * 35))[:35]
                print("{}[{}]{}".format(left,self.tm.symbol,right))
                if (self.tm.statename, self.tm.symbol) in self.tm.states:
                    state = self.tm.states[(self.tm.statename, self.tm.symbol)]
                    print("{} {} {} {} {}".format(self.tm.statename, self.tm.symbol,
                        *self.tm.states[(self.tm.statename, self.tm.symbol)]))
                    if self.tm.statename in self.breakpoints:
                        print(f"Breakpoint (transitions: {self.tm.stepcount})")
                    elif self.tm.looping:
                        print("looping detected")

                else:
                    if self.tm.statename == "HLT":
                        print(f"HALTED (transitions: {self.tm.stepcount})")
                    else:
                        print("Undefined transition: {} {} (transitions: {}"
                              .format(self.tm.statename, self.tm.symbol, self.tm.stepcount))


import argparse

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description="Debugger for Turing machines")
    parser.add_argument("TM_Files", metavar="TM_File", help="Turing Machine file", nargs="*")

    args = parser.parse_args()

    tmdb = TMDB()
    for fname in args.TM_Files:
        tmdb.tm.load(fname)
    tmdb.mainloop()
