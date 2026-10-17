#!/usr/bin/python3

# The tm file format is based on https://schaetzc.github.io/tursi/manual.html
# limitations: #! fill must be a single symbol

from collections import namedtuple

Transition = namedtuple("Transition", ["write", "direction", "nextstate"])

class TuringMachine:
    def __init__(self):
        self.start = "0"
        self.states = {}
        self.statename = "0"
        self.source = {}
        self.sourcemap = {}
        self.left = []
        self.right = []
        self.symbol = "0"
        self.fill = "0"
        self.symbols = set() # symbols seen so far
        self.stepcount = 0
        self.statetrace = [("0", '0', 0)]
        self.looping = False

    def tape_at(self, index):
        if index == 0:
            return self.symbol
        elif index < 0 and len(self.left) >= -index:
            return self.left[len(self.left) + index]
        elif index > 0 and len(self.right) >= index:
            return self.right[len(self.right) - index]
        else:
            return self.fill

    def write_tape_at(self, index, symbol):
        if index == 0:
            self.symbol = symbol
        elif index < 0:
            while len(self.left) <= -index:
                self.left.insert(0, self.fill)
            self.left[len(self.left) + index] = symbol
        else:
            while len(self.right) <= index:
                self.right.insert(0, self.fill)
            self.right[len(self.right) - index] = symbol


    def load(self, filename):
        linenumber = 1
        with open(filename,"r") as f:
            for l in f:
                self.loadline(l, filename, linenumber)
                linenumber = linenumber + 1

    def loadline(self, line, filename, lineno):

        self.source[(filename, lineno)] = line.rstrip()

        if line.startswith("#"):
            if line.startswith("#!"):
                line = line[2:].strip().split()
                if line[0] == "start" and len(line) > 1:
                    self.start = line[1]
                if line[0] == "fill" and len(line) > 1 and len(line[1]) == 1:
                    self.fill = line[1]
                if line[0] == "write" and len(line) == 2:
                    for (i, s) in enumerate(line[1]):
                        self.write_tape_at(i, s)
                if line[0] == "write" and len(line) == 3:
                    if line[2].endswith("<"):
                        for (i, s) in enumerate(line[2]):
                            self.write_tape_at(int(line[1][:-1]) - len(line[2]) + 1 + i, s)
                    else:
                        for (i, s) in enumerate(line[2]):
                            self.write_tape_at(int(line[1]) + i, s)
                if line[0] == "delete" and len(line) == 3:
                    if (line[1], line[2]) in self.states:
                        del self.states[(line[1], line[2])]
                    else:
                        print("state not found")
        elif line.strip() != "":
            #attempt to load as a state transition
            line = line.strip().split()
            if len(line) == 5 and len(line[1]) == 1 and len(line[2]) == 1 and len(line[3]) == 1 and line[3] in "lL<nNsS=rR>":
                self.states[(line[0], line[1])] = Transition(*line[2:])
                self.sourcemap[(line[0], line[1])] = (filename, lineno)
                self.symbols.add(line[1])
                self.symbols.add(line[2])
            else:
                return False

        return True


    def save(self, filename):
        def paddedname(statetuple):
            return (".".join(v.zfill(6) if v.isdigit() else v for v in statetuple[0].split(".")), statetuple[1])

        with open(filename, "w") as f:
            f.write("#! start {}\n".format(self.start))

            for statetuple in sorted(self.states, key=paddedname):
                # print associated comments with the state first
                if statetuple in self.sourcemap:
                    (filename, lineno) = self.sourcemap[statetuple]
                    while (filename, lineno - 1) in self.source and self.source[(filename, lineno - 1)].startswith("#"):
                        lineno = lineno - 1
                    while self.source[(filename, lineno)].startswith("#"):
                        if not self.source[(filename, lineno)].startswith("#!"):
                            f.write("{}\n".format(self.source[(filename, lineno)]))
                        lineno = lineno + 1
                f.write("{} {} {} {} {}\n".format(*statetuple, *self.states[statetuple][:3]))


    def step(self):
        self.looping = False
        try:
            transition = self.states[(self.statename, self.symbol)]
        except KeyError:
            return False
        symbol = transition.write
        if transition.direction in ('l', 'L', '<'):
            self.right.append(symbol)
            if self.left:
                self.symbol = self.left.pop()
            else:
                self.symbol = self.fill
                looping = (self.statename, self.fill) in self.states \
                    and self.states[(self.statename, self.fill)].nextstate == self.statename \
                    and self.states[(self.statename, self.fill)].direction in ('l', 'L', '<')
        elif transition.direction in ('r', 'R', '>'):
            self.left.append(symbol)
            if self.right:
                self.symbol = self.right.pop()
            else:
                self.symbol = self.fill
                looping = (self.statename, self.fill) in self.states \
                    and self.states[(self.statename, self.fill)].nextstate == self.statename \
                    and self.states[(self.statename, self.fill)].direction in ('r', 'R', '>')

        self.statename = transition.nextstate
        if (self.statename, self.symbol) == self.statetrace[0][:2]:
            self.statetrace[0] = (self.statename, self.symbol, self.statetrace[0][2] + 1)
        else:
            self.statetrace = [(self.statename, self.symbol, 1)] + self.statetrace[:10]

        self.stepcount += 1
        return True

    def gc(self):
        """ Returns a list of garbage-collected states"""

        rv = []
        grey = set([self.start, self.statename])
        black = set()

        while grey:
            state = grey.pop()
            if state not in black:
                black.add(state)
                for symbol in self.symbols:
                    if (state, symbol) in self.states:
                        grey.add(self.states[(state, symbol)].nextstate)

        rv = [item for item in self.states.items() if item[0][0] not in black]

        for item in rv:
            del self.states[item[0]]

        return rv
