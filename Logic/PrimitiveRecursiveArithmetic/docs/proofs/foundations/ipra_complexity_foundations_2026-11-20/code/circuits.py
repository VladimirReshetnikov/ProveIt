"""Finite reference implementation: bounded tape verifier -> circuit -> 3-CNF.

The implementation uses a deterministic, single-tape machine with alphabet
{0, 1, blank}. A fixed input prefix is followed by a fixed-width binary
certificate. All time bounds and certificate widths are explicit. The Python
code is a reference artifact, not a proof of its runtime or an iPRA derivation.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, Sequence


BLANK = 2
ALPHABET = (0, 1, BLANK)
Clause = tuple[int, ...]  # signed, one-based DIMACS variable numbers
CNF = tuple[Clause, ...]


@dataclass(frozen=True)
class Gate:
    op: str
    args: tuple[int, ...] = ()  # zero-based wire numbers
    value: bool | None = None


@dataclass(frozen=True)
class Circuit:
    inputs: int
    gates: tuple[Gate, ...]
    output: int

    @property
    def wires(self) -> int:
        return self.inputs + len(self.gates)

    def check(self) -> None:
        if self.inputs < 0 or not 0 <= self.output < self.wires:
            raise ValueError("invalid circuit size or output")
        for i, gate in enumerate(self.gates, self.inputs):
            if gate.op not in {"const", "not", "and"}:
                raise ValueError("unknown gate")
            arity = {"const": 0, "not": 1, "and": 2}[gate.op]
            if len(gate.args) != arity or any(not 0 <= a < i for a in gate.args):
                raise ValueError("gate references a non-earlier wire")
            if gate.op == "const" and not isinstance(gate.value, bool):
                raise ValueError("constant is not Boolean")

    def extend(self, inputs: Sequence[bool]) -> tuple[bool, ...]:
        """Construct the unique assignment satisfying every gate equation."""
        self.check()
        if len(inputs) != self.inputs or any(type(b) is not bool for b in inputs):
            raise ValueError("wrong number/type of input bits")
        values = list(inputs)
        for gate in self.gates:
            if gate.op == "const":
                values.append(bool(gate.value))
            elif gate.op == "not":
                values.append(not values[gate.args[0]])
            else:
                values.append(values[gate.args[0]] and values[gate.args[1]])
        return tuple(values)

    def evaluate(self, inputs: Sequence[bool]) -> bool:
        return self.extend(inputs)[self.output]

    def tseitin(self, require_output: bool = True) -> CNF:
        """At most 3*gate_count+inputs+1 clauses, of width at most three.

        An input tautology makes every original witness variable occur even
        when the circuit ignores it. Occurrence-based variable renaming must
        preserve these variables to preserve the number of witnesses.
        """
        self.check()
        clauses: list[Clause] = [(i + 1, -(i + 1)) for i in range(self.inputs)]
        for i, gate in enumerate(self.gates, self.inputs):
            z = i + 1
            args = tuple(a + 1 for a in gate.args)
            if gate.op == "const":
                clauses.append((z if gate.value else -z,))
            elif gate.op == "not":
                (x,) = args
                clauses.extend(((z, x), (-z, -x)))
            else:
                x, y = args
                clauses.extend(((-z, x), (-z, y), (z, -x, -y)))
        if require_output:
            clauses.append((self.output + 1,))
        return tuple(clauses)

    def restrict(self, assignment: Sequence[bool]) -> tuple[bool, ...]:
        """Extract a witness from a satisfying assignment, rejecting bad codes."""
        if len(assignment) != self.wires or any(type(b) is not bool for b in assignment):
            raise ValueError("wrong assignment shape")
        if not cnf_value(self.tseitin(), assignment):
            raise ValueError("assignment does not satisfy the output CNF")
        return tuple(assignment[: self.inputs])


def cnf_value(cnf: CNF, assignment: Sequence[bool]) -> bool:
    def value(literal: int) -> bool:
        if literal == 0 or abs(literal) > len(assignment):
            raise ValueError("invalid literal")
        bit = assignment[abs(literal) - 1]
        return bit if literal > 0 else not bit

    return all(any(value(literal) for literal in clause) for clause in cnf)


class Builder:
    """Topological wire allocation; identical gates may share an output wire."""

    def __init__(self, inputs: int):
        if inputs < 0:
            raise ValueError("negative input count")
        self.inputs = inputs
        self.gates: list[Gate] = []
        self.cache: dict[Gate, int] = {}

    def add(self, gate: Gate) -> int:
        if gate in self.cache:
            return self.cache[gate]
        wire = self.inputs + len(self.gates)
        if any(not 0 <= a < wire for a in gate.args):
            raise ValueError("non-topological gate")
        self.gates.append(gate)
        self.cache[gate] = wire
        return wire

    def constant(self, value: bool) -> int:
        return self.add(Gate("const", value=value))

    def negate(self, a: int) -> int:
        return self.add(Gate("not", (a,)))

    def conjunction(self, a: int, b: int) -> int:
        return self.add(Gate("and", (a, b)))

    def both(self, *args: int) -> int:
        out = self.constant(True)
        for arg in args:
            out = self.conjunction(out, arg)
        return out

    def either(self, args: Iterable[int]) -> int:
        out = self.constant(False)
        for arg in args:
            out = self.negate(self.conjunction(self.negate(out), self.negate(arg)))
        return out

    def finish(self, output: int) -> Circuit:
        circuit = Circuit(self.inputs, tuple(self.gates), output)
        circuit.check()
        return circuit


@dataclass(frozen=True)
class TapeMachine:
    states: int
    start: int
    accepting: frozenset[int]
    rejecting: frozenset[int]
    transitions: dict[tuple[int, int], tuple[int, int, int]]

    def check(self) -> None:
        if self.states < 1 or not 0 <= self.start < self.states:
            raise ValueError("invalid states")
        if self.accepting & self.rejecting:
            raise ValueError("terminal sets overlap")
        if any(not 0 <= q < self.states for q in self.accepting | self.rejecting):
            raise ValueError("invalid terminal state")
        for q in range(self.states):
            for symbol in ALPHABET:
                nq, written, move = self.delta(q, symbol)
                if not 0 <= nq < self.states or written not in ALPHABET or move not in (-1, 0, 1):
                    raise ValueError("invalid transition")

    def delta(self, state: int, symbol: int) -> tuple[int, int, int]:
        if state in self.accepting | self.rejecting:
            return state, symbol, 0  # terminal states are absorbing
        try:
            return self.transitions[state, symbol]
        except KeyError as exc:
            raise ValueError("nonterminal transition table is incomplete") from exc


@dataclass(frozen=True)
class Configuration:
    state: int
    head: int
    tape: dict[int, int]


def simulate_trace(machine: TapeMachine, word: Sequence[int], steps: int) -> tuple[Configuration, ...]:
    machine.check()
    if steps < 0 or any(bit not in (0, 1) for bit in word):
        raise ValueError("invalid word or clock")
    tape = {i: bit for i, bit in enumerate(word)}
    state, head = machine.start, 0
    trace = [Configuration(state, head, tape.copy())]
    for _ in range(steps):
        state, written, move = machine.delta(state, tape.get(head, BLANK))
        tape[head] = written
        head += move
        trace.append(Configuration(state, head, tape.copy()))
    return tuple(trace)


@dataclass(frozen=True)
class Snapshot:
    positions: tuple[int, ...]
    state: tuple[int, ...]
    head: tuple[int, ...]
    tape: tuple[tuple[int, ...], ...]

    def decode(self, values: Sequence[bool]) -> Configuration:
        def unique(wires: Sequence[int]) -> int:
            active = [i for i, w in enumerate(wires) if values[w]]
            if len(active) != 1:
                raise ValueError("invalid one-hot configuration")
            return active[0]

        return Configuration(unique(self.state), self.positions[unique(self.head)],
                             {p: unique(symbols) for p, symbols in zip(self.positions, self.tape)})


@dataclass(frozen=True)
class CompiledVerifier:
    circuit: Circuit
    snapshots: tuple[Snapshot, ...]
    fixed_input: tuple[int, ...]
    witness_width: int
    steps: int

    def extend_witness(self, witness: Sequence[bool]) -> tuple[bool, ...]:
        return self.circuit.extend(witness)

    def extract_witness(self, assignment: Sequence[bool]) -> tuple[bool, ...]:
        return self.circuit.restrict(assignment)


def compile_verifier(machine: TapeMachine, fixed_input: Sequence[int],
                     witness_width: int, steps: int) -> CompiledVerifier:
    """Unroll the bounded machine into an acyclic Boolean circuit.

    Tape positions range from -steps through len(input)+witness_width+steps.
    At time t<=steps the head lies in [-t,t], so the window cannot truncate
    a reachable configuration. State, head, and each symbol use one-hot wires.
    """
    machine.check()
    if witness_width < 0 or steps < 0 or any(bit not in (0, 1) for bit in fixed_input):
        raise ValueError("invalid compiler parameters")
    fixed_input = tuple(fixed_input)
    n = len(fixed_input) + witness_width
    positions = tuple(range(-steps, n + steps + 1))
    builder = Builder(witness_width)
    zero, one = builder.constant(False), builder.constant(True)
    state = tuple(one if q == machine.start else zero for q in range(machine.states))
    head = tuple(one if p == 0 else zero for p in positions)
    tape_rows: list[tuple[int, ...]] = []
    for p in positions:
        if 0 <= p < len(fixed_input):
            bit = fixed_input[p]
            tape_rows.append(tuple(one if a == bit else zero for a in ALPHABET))
        elif len(fixed_input) <= p < n:
            witness_wire = p - len(fixed_input)
            tape_rows.append((builder.negate(witness_wire), witness_wire, zero))
        else:
            tape_rows.append((zero, zero, one))
    tape = tuple(tape_rows)
    snapshots = [Snapshot(positions, state, head, tape)]
    index = {p: i for i, p in enumerate(positions)}

    for _ in range(steps):
        to_state: list[list[int]] = [[] for _ in range(machine.states)]
        to_head: list[list[int]] = [[] for _ in positions]
        writes: list[list[list[int]]] = [[[] for _ in ALPHABET] for _ in positions]
        for i, p in enumerate(positions):
            for q in range(machine.states):
                for a in ALPHABET:
                    signal = builder.both(head[i], state[q], tape[i][a])
                    nq, written, move = machine.delta(q, a)
                    to_state[nq].append(signal)
                    if p + move in index:
                        to_head[index[p + move]].append(signal)
                    writes[i][written].append(signal)
        new_state = tuple(builder.either(signals) for signals in to_state)
        new_head = tuple(builder.either(signals) for signals in to_head)
        new_tape = tuple(
            tuple(builder.either((
                builder.both(builder.negate(head[i]), tape[i][a]),
                builder.either(writes[i][a]),
            )) for a in ALPHABET) for i, _ in enumerate(positions)
        )
        state, head, tape = new_state, new_head, new_tape
        snapshots.append(Snapshot(positions, state, head, tape))
    output = builder.either(state[q] for q in sorted(machine.accepting))
    return CompiledVerifier(builder.finish(output), tuple(snapshots), fixed_input, witness_width, steps)


def parity_machine() -> TapeMachine:
    """Accept a finite binary word iff its number of 1s is even."""
    transitions = {}
    for parity in (0, 1):
        for symbol in (0, 1):
            transitions[parity, symbol] = (parity ^ symbol, symbol, 1)
        transitions[parity, BLANK] = (2 if parity == 0 else 3, BLANK, 0)
    return TapeMachine(4, 0, frozenset({2}), frozenset({3}), transitions)


if __name__ == "__main__":
    verifier = compile_verifier(parity_machine(), (1, 0), witness_width=2, steps=5)
    witness = (True, False)
    assignment = verifier.extend_witness(witness)
    circuit = verifier.circuit
    print({"input": verifier.fixed_input, "witness": witness,
           "accepts": assignment[circuit.output], "gates": len(circuit.gates),
           "variables": circuit.wires, "clauses": len(circuit.tseitin()),
           "cnf_satisfied": cnf_value(circuit.tseitin(), assignment)})
