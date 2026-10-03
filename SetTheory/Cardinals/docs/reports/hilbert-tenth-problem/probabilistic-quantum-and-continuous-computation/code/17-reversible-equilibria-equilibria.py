"""Exact arithmetic for the birth--death chains in the accompanying article.

All core routines use the Python standard library. Infinite-tail claims are
proved in article.tex, not inferred from a finite computation here.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Iterable, Literal, Sequence


def checked_bits(bits: Iterable[int]) -> tuple[int, ...]:
    out = tuple(bits)
    if any(type(b) is not int or b not in (0, 1) for b in out):
        raise ValueError("Each defect flag must be the integer 0 or 1.")
    return out


def transition_row(n: int, bit: int) -> dict[int, Fraction]:
    """A row of the infinite chain; bit is the defect flag at state n."""
    if type(n) is not int or n < 0:
        raise ValueError("State must be a nonnegative integer.")
    checked_bits((bit,))
    birth = Fraction(2 - bit, 8)
    death = Fraction(1, 2) if n else Fraction(0)
    row = {n: 1 - birth - death, n + 1: birth}
    if n:
        row[n - 1] = death
    return row


@dataclass(frozen=True)
class Prefix:
    bits: tuple[int, ...]
    W: tuple[int, ...]
    S: tuple[int, ...]
    Q: tuple[int, ...]

    @property
    def interval(self) -> tuple[Fraction, Fraction]:
        """Sharp enclosing interval for every continuation of the prefix."""
        w, s, q = self.W[-1], self.S[-1], self.Q[-1]
        return Fraction(q, s + w), Fraction(3 * q, 3 * s + w)

    @property
    def partial_normalizer(self) -> Fraction:
        return Fraction(self.S[-1], self.Q[-1])


def prefix_data(bits: Iterable[int]) -> Prefix:
    bits = checked_bits(bits)
    w, s, q = [1], [1], [1]
    for b in bits:
        w.append((2 - b) * w[-1])
        s.append(4 * s[-1] + w[-1])
        q.append(4 * q[-1])
    return Prefix(bits, tuple(w), tuple(s), tuple(q))


def periodic_normalizer(prefix: Iterable[int], period: Iterable[int]) -> Fraction:
    """Exact Z for a supplied ultimately periodic environment (not a guess)."""
    pre, per = checked_bits(prefix), checked_bits(period)
    if not per:
        raise ValueError("The repeated period must be nonempty.")

    def affine_word(word: tuple[int, ...]) -> tuple[Fraction, Fraction]:
        a, r = Fraction(0), Fraction(1)
        for b in word:
            a += r
            r *= Fraction(2 - b, 4)
        return a, r

    a, r = affine_word(pre)
    ap, rp = affine_word(per)
    return a + r * ap / (1 - rp)


def finite_defect_normalizer(positions: Iterable[int]) -> Fraction:
    ds = tuple(sorted(positions))
    if (any(type(d) is not int or d < 0 for d in ds)
            or len(set(ds)) != len(ds)):
        raise ValueError("Defect positions must be distinct nonnegative integers.")
    return Fraction(2) - sum((Fraction(1, 1 << (d + j))
                             for j, d in enumerate(ds, 1)), Fraction(0))


def single_defect_mass(time: int | None) -> Fraction:
    if time is None:
        return Fraction(1, 2)
    if type(time) is not int or time < 0:
        raise ValueError("Halting time must be nonnegative, or None.")
    return Fraction(1 << (time + 1), (1 << (time + 2)) - 1)


class SearchBudgetExceeded(RuntimeError):
    """An optional operational limit, not a verdict about membership."""


def decode_rational_mass(value: Fraction, *, max_steps: int | None = 100000
                         ) -> tuple[tuple[int, ...], tuple[int, ...]] | None:
    """Decide membership of a rational in the equilibrium Cantor set.

    Return an exact eventually periodic code, or None for nonmembership.
    With max_steps=None this mathematical decision algorithm has no imposed
    step cap. At a cap, raise an exception rather than return a false verdict.
    """
    if not isinstance(value, Fraction):
        raise TypeError("Pass a Fraction, not an approximate float.")
    if value < Fraction(1, 2) or value > Fraction(3, 4):
        return None
    z = 1 / value
    seen: dict[Fraction, int] = {}
    bits: list[int] = []
    while z not in seen:
        if max_steps is not None and len(bits) >= max_steps:
            raise SearchBudgetExceeded("Rational decoder's step limit reached.")
        seen[z] = len(bits)
        if Fraction(4, 3) <= z <= Fraction(3, 2):
            bits.append(1)
            z = 4 * (z - 1)
        elif Fraction(5, 3) <= z <= 2:
            bits.append(0)
            z = 2 * (z - 1)
        else:
            return None
    start = seen[z]
    return tuple(bits[:start]), tuple(bits[start:])


def threshold_witness(data: Prefix, a: int, v: int,
                      direction: Literal["lower", "upper"]) -> dict[str, int] | None:
    """Canonical certificate that the whole prefix cylinder lies on one side.

    lower means pi(0)>a/v, upper means pi(0)<a/v. None means this prefix
    does not certify the assertion; it is not a decision about the limit.
    """
    if type(a) is not int or a < 0 or type(v) is not int or v <= 0:
        raise ValueError("Require a>=0 and v>=1, both integers.")
    if direction not in ("lower", "upper"):
        raise ValueError("Unknown direction.")
    w, s, q = data.W[-1], data.S[-1], data.Q[-1]
    gap = v * q - a * (s + w) if direction == "lower" else a * (3 * s + w) - 3 * v * q
    if gap <= 0:
        return None
    out = {f"W{i}": x for i, x in enumerate(data.W)}
    out.update({f"S{i}": x for i, x in enumerate(data.S)})
    out.update({f"Q{i}": x for i, x in enumerate(data.Q)})
    out["eta"] = gap - 1
    return out


def certificate_residuals(bits: Sequence[int], a: int, v: int,
                          direction: Literal["lower", "upper"],
                          assignment: dict[str, int]) -> list[int]:
    """Residual evaluator. Natural-number and positive-denominator domains matter."""
    bits = checked_bits(bits)
    if type(a) is not int or a < 0 or type(v) is not int or v < 1:
        raise ValueError("Invalid rational threshold.")
    if direction not in ("lower", "upper"):
        raise ValueError("Invalid direction.")
    n = len(bits)
    names = [f"{c}{i}" for c in "WSQ" for i in range(n + 1)] + ["eta"]
    if set(assignment) != set(names):
        raise ValueError("The witness tuple has the wrong coordinates.")
    if any(type(assignment[x]) is not int or assignment[x] < 0 for x in names):
        raise ValueError("Witnesses must be natural numbers.")
    W = [assignment[f"W{i}"] for i in range(n + 1)]
    S = [assignment[f"S{i}"] for i in range(n + 1)]
    Q = [assignment[f"Q{i}"] for i in range(n + 1)]
    rs = [W[0] - 1, S[0] - 1, Q[0] - 1]
    for i, b in enumerate(bits):
        rs.extend((b * (b - 1), W[i + 1] - (2 - b) * W[i],
                   S[i + 1] - 4 * S[i] - W[i + 1], Q[i + 1] - 4 * Q[i]))
    gap = v * Q[n] - a * (S[n] + W[n]) if direction == "lower" else a * (3 * S[n] + W[n]) - 3 * v * Q[n]
    rs.append(gap - 1 - assignment["eta"])
    return rs



def compact_witness(data: Prefix, a: int, v: int,
                    direction: Literal["lower", "upper"]) -> dict[str, int] | None:
    """Eliminate S, Q and W0 from a fixed-horizon certificate."""
    full = threshold_witness(data, a, v, direction)
    if full is None:
        return None
    return {**{f"W{i}": data.W[i] for i in range(1, len(data.W))},
            "eta": full["eta"]}


def compact_residuals(bits: Sequence[int], a: int, v: int,
                      direction: Literal["lower", "upper"],
                      assignment: dict[str, int]) -> list[int]:
    """The N+1-witness, 2N+1-residual fixed-horizon presentation."""
    bits = checked_bits(bits)
    if type(a) is not int or a < 0 or type(v) is not int or v < 1:
        raise ValueError("Invalid rational threshold.")
    if direction not in ("lower", "upper"):
        raise ValueError("Invalid direction.")
    n = len(bits)
    names = [f"W{i}" for i in range(1, n + 1)] + ["eta"]
    if set(assignment) != set(names):
        raise ValueError("The compact witness has the wrong coordinates.")
    if any(type(assignment[x]) is not int or assignment[x] < 0 for x in names):
        raise ValueError("Witnesses must be natural numbers.")
    W = [1] + [assignment[f"W{i}"] for i in range(1, n + 1)]
    S = sum(4**(n-i)*W[i] for i in range(n + 1))
    rs: list[int] = []
    for i, b in enumerate(bits):
        rs += [b*(b-1), W[i+1]-(2-b)*W[i]]
    gap = v*4**n-a*(S+W[n]) if direction == "lower" else a*(3*S+W[n])-3*v*4**n
    rs.append(gap-1-assignment["eta"])
    return rs

@dataclass(frozen=True)
class Instruction:
    kind: Literal["inc", "dec", "halt"]
    register: int = 0
    target: int = 0
    zero_target: int = 0


@dataclass(frozen=True)
class State:
    pc: int
    counters: tuple[int, ...]
    history: int = 0


@dataclass(frozen=True)
class Rule:
    source: int
    target: int
    register: int | None
    delta: int
    guard: Literal["always", "zero", "positive"]
    tag: int


class ReversibleCounterLift:
    """Finite-rule reversible history lift of a deterministic counter program.

    The extra done state continues forever; an original halt state is visited
    exactly once along each halting forward trajectory. Counter arithmetic is
    guarded affine arithmetic, including history'=B*history+tag.
    """
    def __init__(self, program: Sequence[Instruction], registers: int):
        if not program or type(registers) is not int or registers < 1:
            raise ValueError("Need a nonempty program and at least one counter.")
        self.program = tuple(program)
        self.registers = registers
        self.done = len(program)
        rules: list[Rule] = []
        for pc, ins in enumerate(program):
            if ins.kind not in ("inc", "dec", "halt"):
                raise ValueError("Unknown instruction.")
            if ins.kind != "halt":
                if not 0 <= ins.register < registers:
                    raise ValueError("Counter index out of range.")
                if not 0 <= ins.target < len(program):
                    raise ValueError("Target out of range.")
                if ins.kind == "dec" and not 0 <= ins.zero_target < len(program):
                    raise ValueError("Zero target out of range.")
            if ins.kind == "inc":
                specs = [(ins.target, ins.register, 1, "always")]
            elif ins.kind == "dec":
                specs = [(ins.target, ins.register, -1, "positive"),
                         (ins.zero_target, ins.register, 0, "zero")]
            else:
                specs = [(self.done, None, 0, "always")]
            for dst, reg, delta, guard in specs:
                rules.append(Rule(pc, dst, reg, delta, guard, len(rules) + 1))
        rules.append(Rule(self.done, self.done, None, 0, "always", len(rules) + 1))
        self.rules = tuple(rules)
        self.base = len(rules) + 1
        self.by_tag = {r.tag: r for r in rules}

    def _check(self, s: State) -> None:
        if (type(s.pc) is not int or not 0 <= s.pc <= self.done
                or len(s.counters) != self.registers
                or type(s.history) is not int or s.history < 0
                or any(type(x) is not int or x < 0 for x in s.counters)):
            raise ValueError("Malformed state.")

    @staticmethod
    def _enabled(rule: Rule, counters: tuple[int, ...]) -> bool:
        if rule.guard == "always":
            return True
        x = counters[rule.register]  # type: ignore[index]
        return x == 0 if rule.guard == "zero" else x > 0

    def forward(self, s: State) -> State:
        self._check(s)
        possible = [r for r in self.rules if r.source == s.pc and self._enabled(r, s.counters)]
        if len(possible) != 1:
            raise ValueError("Instruction semantics is not deterministic and total.")
        r = possible[0]
        cs = list(s.counters)
        if r.register is not None:
            cs[r.register] += r.delta
        return State(r.target, tuple(cs), self.base * s.history + r.tag)

    def backward(self, s: State) -> State | None:
        self._check(s)
        if s.history == 0:
            return None
        h, tag = divmod(s.history, self.base)
        r = self.by_tag.get(tag)
        if r is None or r.target != s.pc:
            return None
        cs = list(s.counters)
        if r.register is not None:
            cs[r.register] -= r.delta
        if any(x < 0 for x in cs) or not self._enabled(r, tuple(cs)):
            return None
        prev = State(r.source, tuple(cs), h)
        return prev if self.forward(prev) == s else None

    def defect(self, s: State) -> int:
        self._check(s)
        return int(s.pc != self.done and self.program[s.pc].kind == "halt")

    def forward_trace(self, start: State, steps: int) -> tuple[State, ...]:
        if type(steps) is not int or steps < 0:
            raise ValueError("Steps must be a nonnegative integer.")
        out = [start]
        for _ in range(steps):
            out.append(self.forward(out[-1]))
        return tuple(out)


def thue_morse(n: int) -> int:
    if type(n) is not int or n < 0:
        raise ValueError("n must be nonnegative.")
    return n.bit_count() & 1


if __name__ == "__main__":
    data = prefix_data(thue_morse(n) for n in range(80))
    lo, hi = data.interval
    print("Thue--Morse equilibrium enclosure (80 flags):")
    print(lo)
    print(hi)
    print("Width:", hi - lo)
    print("Approximate display only:", float((lo + hi) / 2))
