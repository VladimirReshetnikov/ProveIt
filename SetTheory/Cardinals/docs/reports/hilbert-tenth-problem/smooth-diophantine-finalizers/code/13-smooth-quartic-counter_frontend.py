"""Natural-number quadratic certificates for bounded counter-machine runs."""
from __future__ import annotations
from dataclasses import dataclass
from typing import Sequence
import sympy as sp
from smooth_compiler import QuadraticSystem, exact_int


@dataclass(frozen=True)
class Instruction:
    op: str
    register: int | None = None
    next: int | None = None
    zero: int | None = None


@dataclass(frozen=True)
class Edge:
    source: int
    target: int
    register: int | None
    delta: int
    guard: str


@dataclass(frozen=True)
class Program:
    counters: int
    instructions: tuple[Instruction, ...]

    def __post_init__(self):
        r = exact_int(self.counters, "counter count")
        ins = tuple(self.instructions)
        if r < 1 or not ins:
            raise ValueError("A program needs counters and instructions")
        for i in ins:
            if not isinstance(i, Instruction):
                raise TypeError("Expected Instruction objects")
            if i.op == "halt":
                if any(v is not None for v in (i.register, i.next, i.zero)):
                    raise ValueError("Halt instruction has extraneous fields")
            elif i.op in ("inc", "dec"):
                if i.register is None or not 0 <= exact_int(i.register) < r:
                    raise ValueError("Invalid register")
                if i.next is None or not 0 <= exact_int(i.next) < len(ins):
                    raise ValueError("Invalid next state")
                if i.op == "dec":
                    if i.zero is None or not 0 <= exact_int(i.zero) < len(ins):
                        raise ValueError("Invalid zero target")
                elif i.zero is not None:
                    raise ValueError("Increment instruction has a zero branch")
            else:
                raise ValueError("Unknown opcode")
        if sum(i.op == "halt" for i in ins) != 1:
            raise ValueError("Exactly one absorbing halt state is required")
        object.__setattr__(self, "counters", r)
        object.__setattr__(self, "instructions", ins)

    @property
    def halt(self) -> int:
        return next(i for i, ins in enumerate(self.instructions) if ins.op == "halt")

    @property
    def edges(self) -> tuple[Edge, ...]:
        result = []
        for s, i in enumerate(self.instructions):
            if i.op == "halt":
                result.append(Edge(s, s, None, 0, "any"))
            elif i.op == "inc":
                result.append(Edge(s, i.next, i.register, 1, "any"))
            else:
                result += [Edge(s, i.next, i.register, -1, "positive"),
                           Edge(s, i.zero, i.register, 0, "zero")]
        return tuple(result)

    def run(self, initial: Sequence[int], horizon: int):
        T = exact_int(horizon, "horizon")
        counters = tuple(exact_int(a, "initial counter") for a in initial)
        if T < 0 or len(counters) != self.counters or any(a < 0 for a in counters):
            raise ValueError("Invalid initial counters or horizon")
        state = 0
        history, chosen = [(state, counters)], []
        for _ in range(T):
            enabled = [(k, e) for k, e in enumerate(self.edges) if e.source == state
                       and (e.guard == "any" or
                            (e.guard == "zero" and counters[e.register] == 0) or
                            (e.guard == "positive" and counters[e.register] > 0))]
            if len(enabled) != 1:
                raise ArithmeticError("Program is not deterministic")
            k, e = enabled[0]
            cc = list(counters)
            if e.register is not None:
                cc[e.register] += e.delta
            state, counters = e.target, tuple(cc)
            chosen.append(k)
            history.append((state, counters))
        return tuple(history), tuple(chosen)


@dataclass(frozen=True)
class BoundedCertificate:
    system: QuadraticSystem
    history: tuple
    selected: tuple[int, ...]
    point: tuple[int, ...]
    accepting: bool
    horizon: int


def compile_counter(program: Program, initial: Sequence[int], horizon: int) -> BoundedCertificate:
    if not isinstance(program, Program):
        raise TypeError("Expected a Program")
    history, chosen = program.run(initial, horizon)
    T, ell, r = int(horizon), len(program.instructions), program.counters
    ee = program.edges
    positives = [k for k, e in enumerate(ee) if e.guard == "positive"]
    q = {(s,i): sp.Symbol(f"q_{s}_{i}") for s in range(T+1) for i in range(ell)}
    c = {(s,j): sp.Symbol(f"c_{s}_{j}") for s in range(T+1) for j in range(r)}
    a = {(s,k): sp.Symbol(f"a_{s}_{k}") for s in range(T) for k in range(len(ee))}
    d = {(s,k): sp.Symbol(f"d_{s}_{k}") for s in range(T) for k in positives}
    vv = tuple(q.values()) + tuple(c.values()) + tuple(a.values()) + tuple(d.values())
    residuals, labels = [], []
    def add(label, residual):
        labels.append(label)
        residuals.append(sp.expand(residual))
    for i in range(ell):
        add(f"initial_state_{i}", q[0,i] - int(i == 0))
    for j in range(r):
        add(f"initial_counter_{j}", c[0,j] - history[0][1][j])
    for s in range(T):
        add(f"one_edge_{s}", sum(a[s,k] for k in range(len(ee))) - 1)
        for i in range(ell):
            add(f"source_{s}_{i}", q[s,i]-sum(a[s,k] for k,e in enumerate(ee) if e.source == i))
            add(f"target_{s}_{i}", q[s+1,i]-sum(a[s,k] for k,e in enumerate(ee) if e.target == i))
        for j in range(r):
            add(f"update_{s}_{j}", c[s+1,j]-c[s,j]-sum(e.delta*a[s,k] for k,e in enumerate(ee) if e.register == j))
        for k,e in enumerate(ee):
            if e.guard == "zero":
                add(f"zero_guard_{s}_{k}", a[s,k]*c[s,e.register])
            elif e.guard == "positive":
                add(f"positive_guard_{s}_{k}", a[s,k]*c[s,e.register]-a[s,k]-d[s,k])
    add("accept", q[T, program.halt]-1)
    values = {}
    for s, (state, counters) in enumerate(history):
        values.update({q[s,i]: int(i == state) for i in range(ell)})
        values.update({c[s,j]: counters[j] for j in range(r)})
    for s, k0 in enumerate(chosen):
        values.update({a[s,k]: int(k == k0) for k in range(len(ee))})
        values.update({d[s,k]: history[s][1][ee[k].register]-1 if k == k0 else 0 for k in positives})
    system = QuadraticSystem(vv, tuple(residuals), tuple(labels))
    return BoundedCertificate(system, history, chosen, tuple(values[v] for v in vv),
                              history[-1][0] == program.halt, T)


def countdown() -> Program:
    return Program(1, (Instruction("dec", 0, 0, 1), Instruction("halt")))
