#!/usr/bin/env python3
"""Symbolic finite-word checks for the combined Shift/MP command semantics.

No giant formula or Cantor-stack integer is materialized.  Formula constructors
are exact arithmetic syntax, accompanied only by their elementary zero and
modulo-four facts.  An undecided equality is an error, not a guessed branch.
These checks supplement the universal proof in combined_commands.tex; they do
not certify the binary tape implementation or an end-to-end Lean theorem.
"""
from dataclasses import dataclass
from itertools import product
import json


@dataclass(frozen=True)
class Term:
    op: str
    args: tuple = ()


def variable(name, kind="nonone"):
    # kind=positive, nonone, or arbitrary; no truth of a formula is asserted.
    return Term("var", (name, kind))


def add(a, b):
    if a == 0:
        return b
    if b == 0:
        return a
    if isinstance(a, int) and isinstance(b, int):
        return a + b
    return Term("+", (a, b))


def residue(a):
    if isinstance(a, int):
        return a % 4
    return {"I": 0, "M": 1, "U": 2, "E": 3, "gate": 0}.get(a.op)


def positive(a):
    if isinstance(a, int):
        return a > 0
    if a.op in ("M", "U", "E"):
        return True
    if a.op == "I":
        return positive(a.args[0]) or positive(a.args[1])
    if a.op == "var":
        return a.args[1] == "positive"
    if a.op == "+":
        return positive(a.args[0]) or positive(a.args[1])
    return False


def equal(a, b):
    if a == b:
        return True
    if isinstance(a, int) and isinstance(b, int):
        return False
    ra, rb = residue(a), residue(b)
    if ra is not None and rb is not None and ra != rb:
        return False
    if (a == 0 and positive(b)) or (b == 0 and positive(a)):
        return False
    if a == 1 and isinstance(b, Term) and b.op == "var" and b.args[1] == "nonone":
        return False
    if b == 1 and isinstance(a, Term) and a.op == "var" and a.args[1] == "nonone":
        return False
    raise ValueError(f"Undecided symbolic equality: {a!r} == {b!r}")


def I(a, b):
    return 0 if a == 0 and b == 0 else Term("I", (a, b))


def M(a, b):
    return 1 if a == 0 and b == 0 else Term("M", (a, b))


def U(a, b):
    return Term("U", (a, b))


def E(a, b):
    return Term("E", (a, b))


def N(a):
    return I(a, 1)


def conj(a, b):
    return N(I(a, N(b)))


def ex(a, b):
    return N(U(a, N(b)))


def rho(a, b, c, u):
    return I(I(I(c, u), a), I(I(a, c), I(b, c)))


def heads(D, H, A, d, h):
    return (
        I(U(D, A), I(U(D, I(A, H)), U(D, H))),
        ex(D, E(H, D)),
        I(E(H, D), I(M(A, H), M(A, D))),
        I(M(H, D), I(E(H, A), M(A, D))),
        I(U(D, U(A, H)), U(A, U(D, H))),
        I(ex(D, U(D, H)), H),
        rho(D, A, H, d),
        U(d, h),
    )


def gate(a, b, c):
    # The exact conditional gate is retained as a term; its result is always
    # divisible by four, including a failed guard's literal zero result.
    return Term("gate", (a, b, c))


@dataclass(frozen=True)
class Stack:
    prefix: tuple
    tail: str = "w"

    def prepend(self, xs):
        return Stack(tuple(xs) + self.prefix, self.tail)

    def pop(self):
        if not self.prefix:
            raise ValueError("A proof contract tried to inspect the opaque tail")
        return self.prefix[0], Stack(self.prefix[1:], self.tail)


@dataclass(frozen=True)
class Store:
    t: object
    w: Stack
    d: object
    h: object


SH = ("S",)


def AX(c=0, x=0, y=0):
    return ("A", c, x, y)


def MP(x=0):
    return ("M", x)


def step(command, s):
    if command[0] == "S":
        if equal(s.h, 1):
            return None
        a, w = s.w.pop()
        return Store(s.h, w, s.d, a)
    if command[0] == "M":
        y = add(s.d, command[1])
        if equal(I(s.t, y), s.h):
            return Store(0, s.w, 0, y)
        return Store(0, s.w, y, 0)
    if command[0] == "A":
        _, c, x, y = command
        D, H = add(s.d, x), add(s.h, y)
        return Store(gate(H, D, c), s.w.prepend(heads(D, H, c, s.d, s.h) + (s.t,)), 0, 0)
    raise ValueError(command)


def run(word, s):
    for command in word:
        s = step(command, s)
        if s is None:
            break
    return s


POP = [AX()] + [SH] * 10
PUSH = [AX()] + [SH] * 8 + [MP()]
DISCARD = [MP(1), AX(1)] + [SH] * 9 + [MP()]


def offset(i):
    return [] if i == 0 else [MP(i)]


def generalize(i):
    return PUSH + offset(i) + [SH, AX(i)] + [SH] * 9


def select(j, D, H, A):
    return DISCARD + [AX(A, D, H)] + [SH] * (j + 1) + POP * (8 - j)


def select_rho(a, b, c, u):
    return DISCARD + offset(u) + [AX(b, a - u, c)] + [SH] * 8 + POP


def select_gate(a, b, c):
    return DISCARD + [AX(c, b, a)] + POP * 9


def mp_suffix(b):
    return [SH, SH, MP(b), SH]


def check():
    count = 0
    w = Stack(())
    a = variable("a")
    b = variable("b")
    t = variable("t")
    d = variable("d", "arbitrary")
    h = variable("h", "arbitrary")
    c = variable("c", "arbitrary")
    x = variable("x", "arbitrary")
    y = variable("y", "arbitrary")

    def verify(name, got, want):
        nonlocal count
        if got != want:
            raise AssertionError((name, got, want))
        count += 1

    for top in (0, 1, t):
        s = Store(top, w, d, h)
        verify("AX/Sh8", run([AX(c, x, y)] + [SH] * 8, s),
               Store(rho(add(d, x), c, add(h, y), d), w.prepend((top,)), 0, U(d, h)))
        verify("AX/Sh9", run([AX(c, x, y)] + [SH] * 9, s),
               Store(U(d, h), w, 0, top))
        verify("push", run(PUSH, s), Store(0, w.prepend((top,)), 0, 0))
        verify("pop", run(POP, Store(top, w.prepend((a,)), d, h)),
               None if top == 1 else Store(top, w, 0, a))
        verify("discard", run(DISCARD, Store(top, w, 0, 0)), Store(0, w, 0, 0))
        for i in (0, 1, variable("positive-label", "positive")):
            verify("generalize", run(generalize(i), Store(top, w, 0, 0)),
                   Store(U(i, top), w, 0, 0))

    # Generated head/gate selectors are total even if the incoming top is 1.
    for top in (0, 1, t):
        expected = heads(x, y, c, 0, 0)
        for j in range(1, 7):
            verify("head selector", run(select(j, x, y, c), Store(top, w, 0, 0)),
                   Store(expected[j - 1], w, 0, 0))
        for u in range(3):
            verify("rho selector", run(select_rho(4, 7, 9, u), Store(top, w, 0, 0)),
                   Store(rho(4, 7, 9, u), w, 0, 0))
        verify("gate selector", run(select_gate(a, b, c), Store(top, w, 0, 0)),
               Store(gate(a, b, c), w, 0, 0))

    for aa, bb in product((0, 1, a), (0, 1, b)):
        s = Store(0, w.prepend((aa, I(aa, bb), 0)), 0, 0)
        verify("MP suffix", run(mp_suffix(bb), s),
               None if aa == 1 or bb == 1 else Store(bb, w, 0, 0))
    # The terminal word halts before inspecting its original opaque stack.
    verify("halt from derived one", run(POP, Store(1, w, 0, 0)), None)
    return {
        "status": "pass",
        "symbolic_contract_cases": count,
        "mp_suffix_commands": 4,
        "halt_suffix_commands": 11,
        "proof_scope": "symbolic command identities; no physical-table or Lean claim",
    }


if __name__ == "__main__":
    print(json.dumps(check(), indent=2, sort_keys=True))
