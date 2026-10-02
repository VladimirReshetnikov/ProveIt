#!/usr/bin/env python3
"""Exact counter-machine -> homogeneous circuit -> stochastic game compiler.

Standard library only, Python >= 3.10. All arithmetic is exact. This module
implements the constructions proved in the accompanying article; it is not
a machine-checked proof of them. Variable-sized bounded certificates are
complete quadratic polynomials in factored sum/product representation.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from math import lcm
from typing import Iterable, Sequence
import json
from pathlib import Path


def nat(x: int, name: str) -> int:
    if type(x) is not int or x < 0:
        raise ValueError(f"{name} must be a nonnegative integer")
    return x


def power_two_at_least(x: F | int) -> int:
    n = 1
    while n < x:
        n *= 2
    return n


@dataclass(frozen=True)
class Instruction:
    op: str
    counter: int = 0
    target: int = 0
    zero: int = 0


@dataclass(frozen=True)
class Program:
    counters: int
    instructions: tuple[Instruction, ...]

    def __post_init__(self):
        nat(self.counters, "counters")
        object.__setattr__(self, "instructions", tuple(self.instructions))
        if self.counters < 1 or not self.instructions:
            raise ValueError("a program needs counters and instructions")
        if any(not isinstance(i, Instruction) for i in self.instructions):
            raise ValueError("instructions must be Instruction objects")
        if sum(i.op == "halt" for i in self.instructions) != 1:
            raise ValueError("exactly one absorbing halt instruction is required")
        for i in self.instructions:
            if not isinstance(i, Instruction) or i.op not in {"inc", "dec", "halt"}:
                raise ValueError("unsupported instruction")
            if i.op != "halt":
                if nat(i.counter, "counter") >= self.counters:
                    raise ValueError("counter out of range")
                if nat(i.target, "target") >= len(self.instructions):
                    raise ValueError("target out of range")
                if i.op == "dec" and nat(i.zero, "zero target") >= len(self.instructions):
                    raise ValueError("zero target out of range")

    @property
    def halt(self) -> int:
        return next(j for j, i in enumerate(self.instructions) if i.op == "halt")

    def validate_config(self, state: int, counters: Sequence[int]) -> tuple[int, ...]:
        if nat(state, "state") >= len(self.instructions):
            raise ValueError("state out of range")
        if len(counters) != self.counters:
            raise ValueError("wrong number of counters")
        return tuple(nat(c, "counter value") for c in counters)

    def step(self, state: int, counters: Sequence[int]) -> tuple[int, tuple[int, ...]]:
        cs = list(self.validate_config(state, counters))
        i = self.instructions[state]
        if i.op == "halt":
            return state, tuple(cs)
        if i.op == "inc":
            cs[i.counter] += 1
            return i.target, tuple(cs)
        if cs[i.counter] == 0:
            return i.zero, tuple(cs)
        cs[i.counter] -= 1
        return i.target, tuple(cs)

    def encode(self, state: int, counters: Sequence[int], scale: F = F(1)) -> list[F]:
        cs = self.validate_config(state, counters)
        if scale <= 0:
            raise ValueError("scale must be positive")
        return ([scale] + [scale if j == state else F(0)
                           for j in range(len(self.instructions))]
                + [scale / (1 << c) for c in cs])


@dataclass(frozen=True)
class Gate:
    kind: str
    args: tuple[int, ...]
    coeffs: tuple[F, ...]
    depth: int
    label: str


class Circuit:
    def __init__(self, inputs: int):
        if nat(inputs, "inputs") < 1:
            raise ValueError("at least one input is required")
        self.inputs = inputs
        self.gates = [Gate("input", (), (), 0, f"input_{j}") for j in range(inputs)]
        self.outputs: list[int] = []

    def add(self, kind: str, args: Iterable[int], coeffs=(), label="") -> int:
        args = tuple(args)
        if any(type(j) is not int or not 0 <= j < len(self.gates) for j in args):
            raise ValueError("gate dependencies must precede the gate")
        if kind not in {"lin", "min", "max"}:
            raise ValueError("unsupported gate")
        coeffs = tuple(F(c) for c in coeffs)
        if kind == "lin" and len(coeffs) != len(args):
            raise ValueError("wrong coefficient count")
        if kind != "lin" and (len(args) != 2 or coeffs):
            raise ValueError("min and max gates have exactly two operands")
        idx = len(self.gates)
        depth = 1 + max((self.gates[j].depth for j in args), default=0)
        self.gates.append(Gate(kind, args, coeffs, depth, label or f"gate_{idx}"))
        return idx

    def lin(self, *terms: tuple[int, F | int], label="") -> int:
        return self.add("lin", [j for j, _ in terms], [a for _, a in terms], label)

    def evaluate(self, x: Sequence[F]) -> list[F]:
        if len(x) != self.inputs:
            raise ValueError("wrong input dimension")
        values = list(map(F, x))
        for g in self.gates[self.inputs:]:
            if g.kind == "lin":
                values.append(sum((a * values[j] for j, a in zip(g.args, g.coeffs)), F(0)))
            else:
                values.append((min if g.kind == "min" else max)(values[j] for j in g.args))
        return values

    def apply(self, x: Sequence[F]) -> list[F]:
        vals = self.evaluate(x)
        return [vals[j] for j in self.outputs]


def counter_circuit(program: Program, erase_halt: bool = False) -> Circuit:
    """Implement the homogeneous one-step map, including all inactive gates."""
    m, k = len(program.instructions), program.counters
    c = Circuit(1 + m + k)
    s = 0
    p = [1 + j for j in range(m)]
    counters = [1 + m + j for j in range(k)]
    zero = c.lin(label="constant_zero")
    z = [c.add("max", (zero, c.lin((u, 2), (s, -1))), label=f"zero_test_{j}")
         for j, u in enumerate(counters)]
    branches: list[tuple[int, int, tuple[F, ...]]] = []
    for state, ins in enumerate(program.instructions):
        alpha = [F(1)] * k
        if ins.op == "halt":
            if erase_halt:
                continue
            branches.append((p[state], state, tuple(alpha)))
        elif ins.op == "inc":
            alpha[ins.counter] = F(1, 2)
            branches.append((p[state], ins.target, tuple(alpha)))
        else:
            e0 = c.add("min", (p[state], z[ins.counter]))
            ep = c.add("min", (p[state], c.lin((s, 1), (z[ins.counter], -1))))
            branches.append((e0, ins.zero, tuple(alpha)))
            alpha[ins.counter] = F(2)
            branches.append((ep, ins.target, tuple(alpha)))
    out = [c.lin(*[(e, 1) for e, _, _ in branches], label="live_clock")] if erase_halt else [s]
    for j in range(m):
        out.append(c.lin(*[(e, 1) for e, target, _ in branches if target == j],
                         label=f"next_state_{j}"))
    for i, u in enumerate(counters):
        selected = [c.add("min", (c.lin((e, 2)), c.lin((u, a[i]))))
                    for e, _, a in branches]
        out.append(c.lin(*[(g, 1) for g in selected], label=f"next_counter_{i}"))
    c.outputs = out
    return c


def layer_circuit(original: Circuit) -> Circuit:
    """Insert shared delay copies so each dependency crosses exactly one layer."""
    c = Circuit(original.inputs)
    mapped = {i: i for i in range(original.inputs)}
    lifted: dict[tuple[int, int], int] = {}

    def lift(node: int, depth: int) -> int:
        if c.gates[node].depth == depth:
            return node
        key = node, depth
        if key not in lifted:
            if c.gates[node].depth > depth:
                raise ValueError("cannot move a node to an earlier layer")
            prev = lift(node, depth - 1)
            lifted[key] = c.lin((prev, 1), label=f"delay_{node}_to_{depth}")
        return lifted[key]

    for i, g in enumerate(original.gates[original.inputs:], original.inputs):
        args = [lift(mapped[j], g.depth - 1) for j in g.args]
        mapped[i] = c.add(g.kind, args, g.coeffs, g.label)
    depth = max(g.depth for g in c.gates)
    c.outputs = [lift(mapped[j], depth) for j in original.outputs]
    return c


# An action is an immutable sparse stochastic row: ((destination, probability), ...).
Action = tuple[tuple[int, F], ...]


@dataclass(frozen=True)
class Game:
    owners: tuple[str, ...]  # lin, min, or max
    actions: tuple[tuple[Action, ...], ...]
    reset: F = F(0)
    discount: F = F(1, 2)
    reward: F = F(0)

    def __post_init__(self):
        object.__setattr__(self, "owners", tuple(self.owners))
        object.__setattr__(self, "actions", tuple(tuple(tuple((j, F(p)) for j, p in a)
                                  for a in aa) for aa in self.actions))
        object.__setattr__(self, "reset", F(self.reset))
        object.__setattr__(self, "discount", F(self.discount))
        object.__setattr__(self, "reward", F(self.reward))
        if self.reward < 0:
            raise ValueError("this implementation requires nonnegative common reward")
        n = len(self.owners)
        if not n or len(self.actions) != n or not 0 <= self.reset < 1:
            raise ValueError("invalid game or reset")
        if not 0 < self.discount < 1:
            raise ValueError("discount must lie strictly between zero and one")
        for owner, actions in zip(self.owners, self.actions):
            if owner not in {"lin", "min", "max"}:
                raise ValueError("unknown owner")
            if len(actions) != (1 if owner == "lin" else 2):
                raise ValueError("wrong action count")
            for a in actions:
                if len({j for j, _ in a}) != len(a):
                    raise ValueError("duplicate destination")
                if any(type(j) is not int or not 0 <= j < n or p < 0 for j, p in a):
                    raise ValueError("invalid transition")
                if sum((p for _, p in a), F(0)) != 1:
                    raise ValueError("transition row is not stochastic")

    @property
    def n(self) -> int:
        return len(self.owners)

    @property
    def binary(self) -> int:
        return sum(o != "lin" for o in self.owners)

    def apply(self, v: Sequence[F], discounted=True) -> list[F]:
        if len(v) != self.n:
            raise ValueError("wrong state-vector dimension")
        v = list(map(F, v))
        mean = sum(v, F(0)) / self.n
        out = []
        for owner, aa in zip(self.owners, self.actions):
            values = [sum((p * v[j] for j, p in a), F(0)) for a in aa]
            raw = max(values) if owner == "max" else min(values)
            out.append(((1-self.reset) * raw + self.reset * mean)
                       * (self.discount if discounted else 1)
                       + (self.reward if discounted else 0))
        return out

    def rows(self) -> list[list[dict[int, F]]]:
        out = []
        for aa in self.actions:
            rows = []
            for a in aa:
                row = {j: self.reset / self.n for j in range(self.n)} if self.reset else {}
                for j, p in a:
                    row[j] = row.get(j, F(0)) + (1-self.reset) * p
                rows.append({j: p for j, p in row.items() if p})
            out.append(rows)
        return out

    def integer_rows(self) -> tuple[int, list[list[dict[int, int]]]]:
        rows = self.rows()
        d = lcm(*(p.denominator for aa in rows for a in aa for p in a.values()))
        return d, [[{j: int(d*p) for j, p in a.items()} for a in aa] for aa in rows]

    def export(self) -> dict:
        return {"format": "bellman-game-v1", "states": self.n,
                "discount": str(self.discount), "common_reward": str(self.reward),
                "common_uniform_reset": str(self.reset),
                "owners": self.owners, "base_actions":
                [[[[j, str(p)] for j, p in a] for a in aa] for aa in self.actions]}


@dataclass(frozen=True)
class Compilation:
    program: Program
    circuit: Circuit
    game: Game
    normalizers: tuple[int, ...]
    erase_halt: bool = False

    @property
    def macro(self):
        return len(self.normalizers)

    @property
    def scale(self):
        return self.normalizers[-1]

    @staticmethod
    def plus(g: int) -> int:
        return 1 + 2*g

    @staticmethod
    def minus(g: int) -> int:
        return 2 + 2*g

    @property
    def halt_pair(self):
        return self.plus(1 + self.program.halt), self.plus(0)

    def initialize(self, state: int, counters: Sequence[int], shifted=True) -> list[F]:
        vals = self.circuit.evaluate(self.program.encode(state, counters))
        out = [F(0)] * self.game.n
        for j, (val, g) in enumerate(zip(vals, self.circuit.gates)):
            val /= self.normalizers[g.depth]
            out[self.plus(j)], out[self.minus(j)] = val, -val
        if any(abs(v) > 1 for v in out):
            raise AssertionError("normalization invariant failed")
        return [(v+1)/2 for v in out] if shifted else out


def compile_program(program: Program, reset=F(0), pad=True,
                    erase_halt=False, reward=F(0)) -> Compilation:
    circuit = layer_circuit(counter_circuit(program, erase_halt))
    depth = max(g.depth for g in circuit.gates)
    layer_factors = [1] * (depth+1)
    for g in circuit.gates[circuit.inputs:]:
        budget = sum(map(abs, g.coeffs), F(0)) if g.kind == "lin" else F(1)
        layer_factors[g.depth] = max(layer_factors[g.depth], power_two_at_least(budget))
    normalizers = [1]
    for c in layer_factors[1:]:
        normalizers.append(normalizers[-1]*c)
    count = 1 + 2*len(circuit.gates)
    n = power_two_at_least(count) if pad else count
    owners = ["lin"] * n
    aa: list[tuple[Action, ...]] = [(((0, F(1)),),)] * n
    plus, minus = Compilation.plus, Compilation.minus

    def row(terms: Iterable[tuple[int, F]]) -> Action:
        d: dict[int, F] = {}
        for j, p in terms:
            d[j] = d.get(j, F(0)) + p
        rest = 1-sum(d.values(), F(0))
        if rest < 0:
            raise AssertionError("negative probability slack")
        d[0] = d.get(0, F(0)) + rest
        return tuple(sorted((j, p) for j, p in d.items() if p))

    for j in range(circuit.inputs):
        aa[plus(j)] = (((plus(circuit.outputs[j]), F(1)),),)
        aa[minus(j)] = (((minus(circuit.outputs[j]), F(1)),),)
    for j, g in enumerate(circuit.gates[circuit.inputs:], circuit.inputs):
        c = layer_factors[g.depth]
        if g.kind == "lin":
            aa[plus(j)] = (row(((plus(u) if a >= 0 else minus(u)), abs(a)/c)
                               for u, a in zip(g.args, g.coeffs)),)
            aa[minus(j)] = (row(((minus(u) if a >= 0 else plus(u)), abs(a)/c)
                                for u, a in zip(g.args, g.coeffs)),)
        else:
            owners[plus(j)] = g.kind
            owners[minus(j)] = "max" if g.kind == "min" else "min"
            aa[plus(j)] = tuple(row(((plus(u), F(1,c)),)) for u in g.args)
            aa[minus(j)] = tuple(row(((minus(u), F(1,c)),)) for u in g.args)
    game = Game(tuple(owners), tuple(aa), F(reset), reward=F(reward))
    return Compilation(program, circuit, game, tuple(normalizers), erase_halt)


# Linear polynomials use integer variable indices; -1 denotes their constant term.
Linear = dict[int, int]


def add_term(p: Linear, i: int, a: int):
    if a:
        p[i] = p.get(i, 0) + a
        if not p[i]:
            del p[i]


@dataclass
class QuadraticCertificate:
    labels: list[str]
    squares: list[Linear]
    products: list[tuple[int, int]]
    assignment: list[int]
    metadata: dict

    def evaluate(self, assignment: Sequence[int] | None = None) -> int:
        v = self.assignment if assignment is None else assignment
        if len(v) != len(self.labels) or any(type(x) is not int or x < 0 for x in v):
            raise ValueError("witnesses must be natural numbers of the right arity")
        return sum(sum(a*(1 if j == -1 else v[j]) for j, a in p.items())**2
                   for p in self.squares) + sum(v[u]*v[w] for u, w in self.products)

    def expanded(self) -> dict[tuple[int, ...], int]:
        terms: dict[tuple[int, ...], int] = {}
        for p in self.squares:
            entries = sorted(p.items())
            for h, (i, a) in enumerate(entries):
                for j, b in entries[h:]:
                    mon = tuple(k for k in sorted((i, j)) if k != -1)
                    terms[mon] = terms.get(mon, 0) + a*b*(1 if i == j else 2)
        for u, v in self.products:
            mon = tuple(sorted((u, v)))
            terms[mon] = terms.get(mon, 0) + 1
        return {m: a for m, a in terms.items() if a}

    def export(self, path: Path):
        payload = {"format": "natural-quadratic-certificate-v1", "metadata": self.metadata,
                   "variable_labels": self.labels, "assignment": self.assignment,
                   "squared_linear_forms": [[[j, a] for j, a in sorted(p.items())]
                                             for p in self.squares],
                   "nonnegative_products": self.products,
                   "constant_index": -1}
        path.write_text(json.dumps(payload, indent=2)+"\n")


def certificate(game: Game, A: Sequence[int], T: int,
                pair: tuple[int, int], initial_denominator: int = 1,
                target: F | None = None, consensus: bool = False) -> QuadraticCertificate:
    """Emit Q_T with supplied initial integer numerators A, no hidden constraints.

    The input vector is A/initial_denominator. The default observation is
    coordinate equality; target=q tests that every final coordinate equals q;
    consensus=True tests that all final coordinates agree. Common nonnegative
    rewards and arbitrary rational discounts in (0,1) are supported.
    For discount a/b and probability denominator D, integer coefficients aP
    update X_t = scale*(bD)^t*v_t. All time forcing terms are emitted as integers.
    """
    nat(T, "horizon")
    if nat(initial_denominator, "initial denominator") == 0:
        raise ValueError("initial denominator must be positive")
    if target is not None:
        target = F(target)
        if target < 0 or consensus:
            raise ValueError("invalid point target / consensus combination")
    multiplier = lcm(game.reward.denominator, 1 if target is None else target.denominator)
    scale = initial_denominator * multiplier
    if len(A) != game.n:
        raise ValueError("wrong initial dimension")
    input_A = [nat(a, "input numerator") for a in A]
    A = [multiplier*a for a in input_A]
    if len(pair) != 2 or any(nat(i, "observed state") >= game.n for i in pair):
        raise ValueError("invalid observed pair")
    D, rows = game.integer_rows()
    anum, bden = game.discount.numerator, game.discount.denominator
    rows = [[{j: anum*a for j, a in p.items()} for p in aa] for aa in rows]
    labels, assignment, squares, products = [], [], [], []
    prev: list[int] | None = None
    prev_values = A
    for t in range(T):
        forcing = int(scale*(bden*D)**(t+1)*game.reward)
        values = []
        action_values = []
        for i, aa in enumerate(rows):
            av = [sum(a*prev_values[j] for j, a in p.items()) + forcing for p in aa]
            action_values.append(av)
            values.append(max(av) if game.owners[i] == "max" else min(av))
        curr = list(range(len(labels), len(labels)+game.n))
        labels.extend(f"X_{t+1}_{i}" for i in range(game.n))
        assignment.extend(values)
        for i, aa in enumerate(rows):
            gaps = []
            for h, p in enumerate(aa):
                # lin and min: L - Z; max: Z - L.
                sign = -1 if game.owners[i] == "max" else 1
                lin: Linear = {curr[i]: -sign}
                add_term(lin, -1, sign*forcing)
                for j, a in p.items():
                    add_term(lin, -1 if prev is None else prev[j],
                             sign*a*(A[j] if prev is None else 1))
                if len(aa) == 2:
                    gap = len(labels)
                    gaps.append(gap)
                    labels.append(f"gap_{t}_{i}_{h}")
                    assignment.append(sign*(action_values[i][h]-values[i]))
                    add_term(lin, gap, -1)
                squares.append(lin)
            if gaps:
                products.append(tuple(gaps))
        prev, prev_values = curr, values
    endpoints = [(i, None) for i in range(game.n)] if target is not None else (
        [(i, 0) for i in range(1, game.n)] if consensus else [pair])
    for i, j in endpoints:
        terminal: Linear = {}
        add_term(terminal, -1 if prev is None else prev[i], A[i] if prev is None else 1)
        if j is None:
            add_term(terminal, -1, -int(scale*(bden*D)**T*target))
        else:
            add_term(terminal, -1 if prev is None else prev[j], -(A[j] if prev is None else 1))
        squares.append(terminal)
    info = {"states": game.n, "binary_states": game.binary, "horizon": T,
            "probability_denominator": D, "step_denominator": bden*D,
            "discount_numerator": anum, "initial_numerators": A,
            "input_numerators": input_A, "initial_denominator": initial_denominator,
            "witness_scale": scale, "common_reward": str(game.reward),
            "terminal_mode": "point" if target is not None else "consensus" if consensus else "pair",
            "target": None if target is None else str(target),
            "endpoint_squares": len(endpoints),
            "observed_pair": pair, "witnesses": len(labels),
            "squares": len(squares), "products": len(products), "degree_at_most": 2}
    return QuadraticCertificate(labels, squares, products, assignment, info)


def integer_numerators(v: Sequence[F]) -> tuple[int, list[int]]:
    d = lcm(*(F(x).denominator for x in v))
    return d, [int(d*x) for x in v]


def write_game(compilation: Compilation, path: Path, state=0, counters=None):
    if counters is None:
        counters = [0]*compilation.program.counters
    payload = compilation.game.export()
    payload.update({"initial_terminal_payoffs": list(map(str, compilation.initialize(state, counters))),
                    "observed_pair": compilation.halt_pair,
                    "macro_period": compilation.macro,
                    "normalization_scale": compilation.scale,
                    "normalizers": compilation.normalizers, "erase_halt": compilation.erase_halt,
                    "note": "Toy instance, not a numerical universal-machine table."})
    path.write_text(json.dumps(payload, indent=2)+"\n")


def matrix_game(matrix: Sequence[Sequence[int]], vector: Sequence[int],
                reset=F(1, 2)) -> tuple[Game, list[F], tuple[int, int], int]:
    """Skolem instance (A,x), observable (A^n x)[0], to a chance-only game.

    All base probabilities are dyadic; padding and a half-uniform reset keep
    that property and make every transition probability >= 1/(2N).
    """
    d = len(vector)
    if not d or len(matrix) != d or any(len(row) != d for row in matrix):
        raise ValueError("matrix must be square and match the vector")
    if any(type(a) is not int for row in matrix for a in row) or any(type(a) is not int for a in vector):
        raise ValueError("integer matrix and vector required")
    C = power_two_at_least(max(sum(abs(a) for a in row) for row in matrix))
    R = power_two_at_least(max(map(abs, vector)))
    n = power_two_at_least(2*d+1)
    aa: list[tuple[Action, ...]] = [(((0, F(1)),),)]*n
    for i, line in enumerate(matrix):
        for sign in (0, 1):
            probs: dict[int, F] = {}
            for j, a in enumerate(line):
                dest = 1+2*j+((a < 0) ^ bool(sign))
                if a:
                    probs[dest] = F(abs(a), C)
            slack = 1-sum(probs.values(), F(0))
            if slack:
                probs[0] = slack
            aa[1+2*i+sign] = (tuple(sorted(probs.items())),)
    game = Game(tuple(["lin"]*n), tuple(aa), F(reset))
    w = [F(0)]*n
    for i, x in enumerate(vector):
        w[1+2*i], w[2+2*i] = F(x, R), -F(x, R)
    return game, [(a+1)/2 for a in w], (1, 0), C
