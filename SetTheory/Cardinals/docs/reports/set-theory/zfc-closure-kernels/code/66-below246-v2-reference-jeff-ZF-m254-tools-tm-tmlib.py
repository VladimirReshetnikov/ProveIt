"""Own parser/simulator for the zfc_254 tables (format: state read write dir next)."""
import sys

def load(path):
    T = {}
    start = None
    for line in open(path):
        line = line.strip()
        if not line:
            continue
        if line.startswith('#!'):
            parts = line.split()
            if parts[1] == 'start':
                start = parts[2]
            continue
        s, r, w, d, n = line.split()
        assert (s, int(r)) not in T
        assert d in 'LR'
        T[(s, int(r))] = (int(w), d, n)
    return T, start

class Run:
    def __init__(self, T, state, tape=None, head=0):
        self.T = T; self.state = state; self.tape = dict(tape or {}); self.head = head; self.t = 0
    def step(self):
        r = self.tape.get(self.head, 0)
        key = (self.state, r)
        if key not in self.T:
            return False
        w, d, n = self.T[key]
        if w: self.tape[self.head] = 1
        else: self.tape.pop(self.head, None)
        self.head += 1 if d == 'R' else -1
        self.state = n; self.t += 1
        return True
    def ones(self):
        return sorted(self.tape)
    def show(self, lo=None, hi=None):
        o = self.ones()
        lo = min(o + [self.head]) - 1 if lo is None else lo
        hi = max(o + [self.head]) + 1 if hi is None else hi
        s = ''.join(('[%d]' if i == self.head else '%d') % self.tape.get(i, 0) for i in range(lo, hi + 1))
        return '%s @%d t=%d lo=%d: %s' % (self.state, self.head, self.t, lo, s)
