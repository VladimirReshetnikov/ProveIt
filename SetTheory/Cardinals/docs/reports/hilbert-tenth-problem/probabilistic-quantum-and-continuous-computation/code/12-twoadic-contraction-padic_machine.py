"""Exact contracting 2-adic simulation of binary Turing machines.

Only nonnegative Python integers are used for full-value evaluation. The
residue evaluator and the Mealy transducer also specify the map on Z_2.
No external dependencies. Python 3.10+.
"""
from __future__ import annotations
from dataclasses import dataclass
from collections import deque
from typing import Callable, Iterable
import json


def natural(n: int, name: str = "value") -> int:
    if not isinstance(n, int) or isinstance(n, bool) or n < 0:
        raise ValueError(f"{name} must be a nonnegative integer")
    return n


def valuation(n: int) -> int:
    natural(n)
    if n == 0:
        raise ValueError("valuation(0) is infinite, not a Python integer")
    return (n & -n).bit_length() - 1


def interleave(left: int, right: int) -> int:
    natural(left, "left"); natural(right, "right")
    result = 0
    i = 0
    while left or right:
        result |= (left & 1) << (2*i)
        result |= (right & 1) << (2*i+1)
        left >>= 1; right >>= 1; i += 1
    return result


def deinterleave(n: int) -> tuple[int, int]:
    natural(n)
    left = right = i = 0
    while n:
        left |= (n & 1) << i
        right |= ((n >> 1) & 1) << i
        n >>= 2; i += 1
    return left, right


@dataclass(frozen=True)
class Rule:
    target: int
    write: int
    move: str


class Machine:
    def __init__(self, states: int, start: int, halt: int,
                 rules: dict[tuple[int, int], Rule]):
        if states < 2 or not 0 <= start < states or not 0 <= halt < states:
            raise ValueError("need >=2 states and valid start/halt labels")
        self.m, self.start, self.halt = states, start, halt
        self.r = max(1, (states-1).bit_length())
        self.K = self.r + 3
        self.rules = dict(rules)
        for q in range(states):
            if q == halt:
                continue
            for b in (0, 1):
                rule = self.rules.get((q, b))
                if rule is None or not 0 <= rule.target < states:
                    raise ValueError(f"missing/invalid rule for {(q,b)}")
                if rule.write not in (0, 1) or rule.move not in ("L", "R", "S"):
                    raise ValueError("invalid write symbol or move")

    def encode(self, q: int, left: int, right: int) -> int:
        if not 0 <= q < 2**self.r:
            raise ValueError("state label does not fit header")
        return 1 + 2*q + (1 << (self.r+1))*interleave(left, right)

    def decode(self, unit: int) -> tuple[int, int, int]:
        natural(unit)
        if not unit & 1:
            raise ValueError("expected an odd unit")
        data = unit >> 1
        q = data & ((1 << self.r)-1)
        left, right = deinterleave(data >> self.r)
        return q, left, right

    def step(self, q: int, left: int, right: int) -> tuple[int, int, int]:
        """Ordinary TM step; the halt state is padded by identity steps."""
        natural(left); natural(right)
        if not 0 <= q < self.m:
            raise ValueError("invalid machine state")
        if q == self.halt:
            return q, left, right
        a, b = left & 1, right & 1
        A, B = left >> 1, right >> 1
        rule = self.rules[(q, b)]
        w = rule.write
        if rule.move == "R":
            return rule.target, 2*left+w, B
        if rule.move == "L":
            return rule.target, A, a+2*w+4*B
        return rule.target, left, w+2*B

    def unit_step(self, unit: int) -> int:
        q, left, right = self.decode(unit)
        if q >= self.m or q == self.halt:
            return 0
        return self.encode(*self.step(q, left, right))

    def apply(self, n: int, clock: Callable[[int], int] | None = None,
              max_output_bits: int = 1_000_000) -> int:
        natural(n)
        if n == 0:
            return 0
        t = valuation(n)
        h = t+self.K if clock is None else natural(clock(t), "clock output")
        if h < t+self.K:
            raise ValueError("clock must satisfy h(t) >= t+K")
        u = self.unit_step(n >> t)
        if u == 0:
            return 0
        if h+u.bit_length() > max_output_bits:
            raise OverflowError("use residue evaluation or a larger bit budget")
        return u << h

    def residue(self, residue: int, precision: int,
                clock: Callable[[int], int] | None = None) -> int:
        """Compute F(x) mod 2**precision from x mod 2**precision."""
        natural(precision, "precision"); natural(residue, "residue")
        if precision == 0:
            return 0
        n = residue % (1 << precision)
        if n == 0:
            return 0
        t = valuation(n)
        h = t+self.K if clock is None else natural(clock(t), "clock output")
        if h < t+self.K:
            raise ValueError("inadmissible clock")
        if h >= precision:
            return 0
        return (self.unit_step(n >> t) << h) % (1 << precision)

    def description(self) -> dict:
        return {"states": self.m, "start": self.start, "halt": self.halt,
                "r": self.r, "K": self.K,
                "rules": [{"state": q, "read": b, "target": rule.target,
                           "write": rule.write, "move": rule.move}
                          for (q,b), rule in sorted(self.rules.items())]}


class MealyCompiler:
    """Finite-state streaming realization of the constant-drift map.

    Input/output are least-significant-digit first. States are immutable
    tuples. A bootstrap remembers only a bounded prefix; steady states store
    K+2 input bits, a head direction, and one parity bit. Leading zeros do not
    increase the state space.
    """
    initial = ("lead",)

    def __init__(self, machine: Machine):
        self.M = machine
        self.I = machine.K + machine.r + 5

    def transition(self, state: tuple, digit: int) -> tuple[tuple, int]:
        if digit not in (0, 1):
            raise ValueError("binary digit required")
        M, K = self.M, self.M.K
        if state[0] == "lead":
            return (self.initial, 0) if digit == 0 else (("boot", 1, 1), 0)
        if state[0] == "zero":
            return state, 0
        if state[0] == "boot":
            _, i, prefix = state  # i is the index of the new input digit
            prefix |= digit << i
            out = 0 if i < K else (M.unit_step(prefix) >> (i-K)) & 1
            if i >= M.r:
                q, left, right = M.decode(prefix)
                if q >= M.m or q == M.halt:
                    return ("zero",), out
            if i+1 == self.I:
                q, left, right = M.decode(prefix)
                direction = M.rules[(q, right & 1)].move
                buffer = (prefix >> (self.I-(K+2))) & ((1 << (K+2))-1)
                return ("steady", direction, 0, buffer), out
            return ("boot", i+1, prefix), out
        if state[0] == "steady":
            _, direction, parity, buffer = state
            block = buffer | (digit << (K+2))
            if direction == "S":
                delta = 0
            elif direction == "R":
                delta = -2 if parity == 0 else 2
            else:
                delta = 2 if parity == 0 else -2
            out = (block >> (2+delta)) & 1
            return ("steady", direction, 1-parity, block >> 1), out
        raise ValueError("unknown transducer state")

    def run(self, digits: Iterable[int]) -> list[int]:
        state = self.initial
        result = []
        for digit in digits:
            state, out = self.transition(state, digit)
            result.append(out)
        return result

    def table(self, max_states: int = 200_000) -> dict:
        states = [self.initial]
        index = {self.initial: 0}
        transitions = []
        pending = deque([self.initial])
        while pending:
            state = pending.popleft()
            row = []
            for digit in (0, 1):
                target, out = self.transition(state, digit)
                if target not in index:
                    if len(states) >= max_states:
                        raise OverflowError("state budget exceeded")
                    index[target] = len(states); states.append(target); pending.append(target)
                row.append({"target": index[target], "output": out})
            transitions.append(row)
        return {"initial": 0, "alphabet": [0,1], "lsb_first": True,
                "machine": self.M.description(), "states": states,
                "transitions": transitions}


def demo_machine() -> Machine:
    """A NONUNIVERSAL test machine: erase a run of ones, then move left and halt."""
    return Machine(3, 0, 2, {
        (0,0): Rule(1,1,"L"), (0,1): Rule(0,0,"R"),
        (1,0): Rule(2,1,"S"), (1,1): Rule(2,0,"L")})


if __name__ == "__main__":
    M = demo_machine()
    n = M.encode(M.start, 0, 7)
    for j in range(8):
        print(j, n, None if n == 0 else valuation(n))
        n = M.apply(n)
