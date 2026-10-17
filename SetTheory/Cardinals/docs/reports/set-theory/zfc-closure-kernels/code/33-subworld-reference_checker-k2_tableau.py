"""Reference semidecision procedure for the raw K2+ kernel; no TM state claim.

All logical failures return False.  Host failures (including MemoryError) are
deliberately NOT caught.  Syntax decoding and certificate checking are iterative.
Only Python's standard library is used.  See README.md for the exact contract.
"""
from dataclasses import dataclass
from itertools import count
from math import isqrt

BOT, MEM, EQ, IMP, ALL = range(5)


def pair(x, y):
    return (x + y) * (x + y + 1) // 2 + y


def unpair(n):
    w = (isqrt(8 * n + 1) - 1) // 2
    y = n - w * (w + 1) // 2
    return w - y, y


def list_code(xs):
    n = 0
    for x in reversed(xs):
        n = 1 + pair(x, n)
    return n


def decode_list(n):
    xs = []
    while n:
        x, n = unpair(n - 1)
        xs.append(x)
    return xs


class Syntax:
    """An arena of immutable nodes; children always precede their parents."""
    def __init__(self):
        self.nodes, self.free, self.intern = [], [], {}
        self.bot = self.node(BOT)

    def node(self, op, x=0, y=0):
        t = (op, x, y)
        if t not in self.intern:
            if op == BOT:
                fv = frozenset()
            elif op in (MEM, EQ):
                fv = frozenset((x, y))
            elif op == IMP:
                fv = self.free[x] | self.free[y]
            elif op == ALL:
                fv = self.free[y] - {x}
            else:
                raise ValueError("unknown syntax constructor")
            self.intern[t] = len(self.nodes)
            self.nodes.append(t)
            self.free.append(fv)
        return self.intern[t]

    def mem(self, x, y): return self.node(MEM, x, y)
    def eq(self, x, y): return self.node(EQ, x, y)
    def imp(self, a, b): return self.node(IMP, a, b)
    def all(self, v, a): return self.node(ALL, v, a)
    def neg(self, a): return self.imp(a, self.bot)
    def ex(self, v, a): return self.neg(self.all(v, self.neg(a)))
    def conj(self, a, b): return self.neg(self.imp(a, self.neg(b)))
    def iff(self, a, b): return self.conj(self.imp(a, b), self.imp(b, a))

    def quantify(self, vs, f):
        for v in reversed(vs):
            f = self.all(v, f)
        return f

    def decode(self, n):
        """Every natural denotes a formula. Recursive child codes are < n."""
        done, todo = {}, [(n, False)]
        while todo:
            k, ready = todo.pop()
            if k in done:
                continue
            if k == 0:
                done[k] = self.bot
                continue
            tag, p = unpair(k - 1)
            if tag < 2:
                x, y = unpair(p)
                done[k] = self.node(MEM if tag == 0 else EQ, x, y)
            elif tag == 2:
                x, y = unpair(p)
                if ready:
                    done[k] = self.imp(done[x], done[y])
                else:
                    todo.extend(((k, True), (y, False), (x, False)))
            elif ready:
                done[k] = self.all(tag - 3, done[p])
            else:
                todo.extend(((k, True), (p, False)))
        return done[n]

    def code(self, f):
        reached, todo = set(), [f]
        while todo:
            j = todo.pop()
            if j in reached:
                continue
            reached.add(j)
            op, x, y = self.nodes[j]
            if op == IMP: todo.extend((x, y))
            elif op == ALL: todo.append(y)
        codes = {}
        for j in sorted(reached):
            op, x, y = self.nodes[j]
            if op == BOT: n = 0
            elif op in (MEM, EQ): n = 1 + pair(op - MEM, pair(x, y))
            elif op == IMP: n = 1 + pair(2, pair(codes[x], codes[y]))
            else: n = 1 + pair(x + 3, codes[y])
            codes[j] = n
        return codes[f]


class InvalidMatrix(Exception):
    pass


def kernel_components(s, phi):
    if not s.free[phi] <= {0, 1, 2}:
        raise InvalidMatrix("matrix free variables must be among a,b,z")
    A, B = s.mem(2, 4), s.mem(2, 3)
    exact = s.conj(s.imp(A, s.conj(B, phi)),
                   s.imp(B, s.imp(phi, A)))
    ss = s.ex(4, s.conj(s.mem(4, 5),
              s.imp(s.mem(3, 5), s.all(2, exact))))
    red = s.imp(s.mem(0, 5), s.imp(s.mem(1, 5),
          s.imp(phi, s.ex(2, s.conj(s.mem(2, 5), phi)))))
    return ss, red


def kernel_sentence(s, matrices, extensionality=False):
    """One shared existential W, four matrix occurrences per pool member."""
    body = None
    for phi in reversed(matrices):
        ss, red = kernel_components(s, phi)
        row = s.quantify((0, 1, 3, 2), s.conj(ss, red))
        body = row if body is None else s.conj(row, body)
    if body is None:
        body = s.imp(s.bot, s.bot)  # Empty conjunction is true.
    if extensionality:
        ext = s.imp(s.all(2, s.iff(s.mem(2, 0), s.mem(2, 1))), s.eq(0, 1))
        body = s.conj(s.quantify((0, 1), ext), body)
    return s.ex(5, body)


@dataclass
class Branch:
    entries: list                 # (truth sign, formula ID, environment dict)
    next_parameter: int = 1        # 0 initially witnesses the nonempty domain.


def clash(s, branch):
    """Identity equality, including its congruence action on membership."""
    parent = list(range(branch.next_parameter))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    atoms = []
    for sign, f, env in branch.entries:
        op, x, y = s.nodes[f]
        if op == BOT and sign:
            return True
        if op in (MEM, EQ):
            x, y = env[x], env[y]
            atoms.append((sign, op, x, y))
            if op == EQ and sign:
                parent[find(x)] = find(y)
    positive, negative = set(), set()
    for sign, op, x, y in atoms:
        x, y = find(x), find(y)
        if op == EQ and not sign and x == y:
            return True
        if op == MEM:
            (positive if sign else negative).add((x, y))
    return not positive.isdisjoint(negative)


# Instructions: CLOSE, true implication, false implication, true all, false all.
CLOSE, T_IMP, F_IMP, T_ALL, F_ALL = range(5)


def instruction(rule, index=0, parameter=0):
    return pair(rule, pair(index, parameter))


def refutes(s, sentence, certificate):
    """Check a depth-first closed tableau whose root asserts the sentence."""
    if s.free[sentence]:
        return False
    stack = [Branch([(True, sentence, {})])]
    for encoded in certificate:
        if type(encoded) is not int or encoded < 0 or not stack:
            return False
        rule, args = unpair(encoded)
        index, parameter = unpair(args)
        b = stack[-1]
        if rule == CLOSE:
            if index or parameter or not clash(s, b):
                return False
            stack.pop()
            continue
        if rule not in (T_IMP, F_IMP, T_ALL, F_ALL) or index >= len(b.entries):
            return False
        sign, f, env = b.entries[index]
        op, x, y = s.nodes[f]
        if rule != T_ALL and parameter:
            return False
        rest = b.entries[:index] + b.entries[index + 1:]
        if rule == T_IMP and op == IMP and sign:
            stack[-1] = Branch(rest + [(True, y, env)], b.next_parameter)
            stack.append(Branch(rest + [(False, x, env)], b.next_parameter))
        elif rule == F_IMP and op == IMP and not sign:
            b.entries = rest + [(True, x, env), (False, y, env)]
        elif rule == T_ALL and op == ALL and sign and parameter < b.next_parameter:
            b.entries.append((True, y, env | {x: parameter}))
        elif rule == F_ALL and op == ALL and not sign:
            b.entries = rest + [(False, y, env | {x: b.next_parameter})]
            b.next_parameter += 1
        else:
            return False
    return not stack


def candidate_code(matrix_codes, certificate):
    return 1 + pair(list_code(matrix_codes), list_code(certificate))


def check_code(n, extensionality=False):
    """Total on naturals mathematically; resource exhaustion propagates."""
    if type(n) is not int or n <= 0:
        return False
    pool, proof = unpair(n - 1)
    s = Syntax()
    matrices = [s.decode(k) for k in decode_list(pool)]
    try:
        sentence = kernel_sentence(s, matrices, extensionality)
    except InvalidMatrix:
        return False
    return refutes(s, sentence, decode_list(proof))


def first_refutation(extensionality=False):
    """Fair, deliberately impractical enumeration; runs forever if consistent."""
    for n in count():
        if check_code(n, extensionality):
            return n
