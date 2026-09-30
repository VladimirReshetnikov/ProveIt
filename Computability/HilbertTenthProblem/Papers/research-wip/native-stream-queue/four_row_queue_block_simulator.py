#!/usr/bin/env python3
"""Explicit finite-controller simulator for 00,01,12,20 physical queue rows.

Input block coding and finite-controller arithmetic certification are separate
obligations. Every sweep boundary in the compiled controller is recognized by
an encoded delimiter, never by the physical queue length.
"""
import argparse
from collections import deque
from itertools import product
import json
from pathlib import Path
import random

ROWS = {(0, 0), (0, 1), (1, 2), (2, 0)}


class Compiler:
    def __init__(self, alphabet_size, states, halt, transitions, binary=False):
        self.alphabet_size = alphabet_size
        self.binary = binary
        self.active = 1 if binary else 2
        self.rows = {(0, 0), (0, 1), (1, 0)} if binary else ROWS
        self.states = states
        self.halt = frozenset(halt)
        self.transitions = transitions
        self.guard, self.marker = alphabet_size, alphabet_size + 1
        self.codes = {a: 2*a for a in range(alphabet_size + 2)}
        self.decode = {v: a for a, v in self.codes.items()}
        width = max(2, max(self.codes.values()).bit_length())
        self.k = width + width % 2

    def state(self, mode, source, index=0, value=0, end=False):
        return mode, source, index, value, end

    def initial(self, source=0):
        return self.state('read', source)

    def source_options(self, state, symbol):
        if state in self.halt:
            return ((state, symbol),)
        return self.transitions.get((state, symbol), ())

    def step(self, state, read):
        """All controller transitions on one trit; no width argument exists."""
        mode, source, index, value, end = state
        k = self.k
        if mode in ('read', 'erase'):
            if read not in (0, self.active):
                return ()
            value |= (read // self.active) << index
            if index + 1 < k:
                return ((0, self.state(mode, source, index + 1, value)),)
            if value not in self.decode:
                return ()
            symbol = self.decode[value]
            end = symbol == self.marker
            if mode == 'erase':
                return ((0, self.state('erase_blank', source, end=end)),)
            options = (((source, symbol),) if symbol in (self.guard, self.marker)
                       else self.source_options(source, symbol))
            return tuple((0, self.state('write', target, value=self.codes[out], end=end))
                         for target, out in options)
        if mode == 'write':
            if read != 0:
                return ()
            append = (value >> index) & 1
            following = (self.state('write', source, index + 1, value, end)
                         if index + 1 < k else
                         self.state('skip' if end else 'read', source))
            return ((append, following),)
        if mode == 'skip':
            if read != 0:
                return ()
            following = (self.state('skip', source, index + 1)
                         if index + 1 < k else self.state(
                             ('erase' if source in self.halt else 'read')
                             if self.binary else 'prepare', source))
            return ((0, following),)
        if mode == 'prepare':
            if read not in (0, 1):
                return ()
            value |= read << index
            if index + 1 < k:
                following = self.state('prepare', source, index + 1, value)
            else:
                if value not in self.decode:
                    return ()
                following = self.state('prepare_blank', source,
                                       end=self.decode[value] == self.marker)
            return ((2*read, following),)
        if mode in ('prepare_blank', 'erase_blank'):
            if read != 0:
                return ()
            if index + 1 < k:
                following = self.state(mode, source, index + 1, end=end)
            elif mode == 'erase_blank':
                following = self.state('finish' if end else 'erase', source)
            elif not end:
                following = self.state('prepare', source)
            else:
                following = self.state('erase' if source in self.halt else 'read', source)
            return ((0, following),)
        if mode == 'finish':
            if read != 0:
                return ()
            following = (self.state('finish', source, 1) if index == 0
                         else self.state('done', source))
            return ((0, following),)
        assert mode == 'done'
        return ()

    def encoded(self, word, active_multiplier=None):
        if active_multiplier is None:
            active_multiplier = self.active
        digits = []
        for symbol in (*word, self.guard, self.marker):
            digits.extend(active_multiplier*((self.codes[symbol] >> j) & 1)
                          for j in range(self.k))
            digits.extend([0]*self.k)
        return tuple(digits)

    def controller_graph(self):
        """Compile the fixed finite table without inspecting any queue."""
        pending, seen, edges = deque([self.initial()]), {self.initial()}, 0
        while pending:
            state = pending.popleft()
            for read in range(3):
                for append, target in self.step(state, read):
                    assert (read, append) in self.rows
                    assert 0 <= target[2] < self.k
                    assert 0 <= target[3] < 2**self.k
                    edges += 1
                    if target not in seen:
                        seen.add(target)
                        pending.append(target)
        return len(seen), edges


def source_reachable(machine, word):
    start = (word, 0)
    pending, seen = deque([start]), {start}
    while pending:
        queue, state = pending.popleft()
        if state in machine.halt:
            return True
        for target, append in machine.source_options(state, queue[0]):
            item = queue[1:] + (append,), target
            if item not in seen:
                seen.add(item)
                pending.append(item)
    return False


def physical_reachable(machine, word):
    queue = machine.encoded(word)
    start = queue, machine.initial()
    pending, seen = deque([start]), {start}
    zero_count = 0
    while pending:
        queue, state = pending.popleft()
        if not any(queue):
            # Double sentinels prevent every pre-halt zero-queue event.
            assert state[1] in machine.halt
            assert state[0] in ('erase', 'erase_blank', 'finish', 'done')
            zero_count += 1
        if state[0] == 'done':
            assert not any(queue)
            return True, len(seen), zero_count
        for append, target in machine.step(state, queue[0]):
            assert (queue[0], append) in machine.rows
            item = queue[1:] + (append,), target
            if item not in seen:
                seen.add(item)
                pending.append(item)
    return False, len(seen), zero_count


def deterministic_trace(machine, word):
    queue, state = machine.encoded(word), machine.initial()
    trace, cycles, m = [], 0, len(queue)
    logical, source = tuple(word), 0
    cycle_length = (m if machine.binary else 2*m) + machine.k
    while state[0] != 'done':
        assert len(trace) < 100000  # Fixture assertion, not a decision cutoff.
        if len(trace) == cycles*cycle_length and state[0] == 'read':
            expected = []
            for a in logical:
                options = machine.source_options(source, a)
                assert len(options) == 1
                source, b = options[0]
                expected.append(b)
            logical = tuple(expected)
            end_cycle = len(trace) + cycle_length
        choices = machine.step(state, queue[0])
        assert len(choices) == 1
        append, following = choices[0]
        trace.append((queue[0], append))
        queue, state = queue[1:] + (append,), following
        if len(trace) == end_cycle:
            assert queue == machine.encoded(logical)
            assert state[1] == source
            assert state[0] == ('erase' if source in machine.halt else 'read')
            cycles += 1
        if not any(queue):
            assert state[1] in machine.halt
    assert len(trace) == cycles*cycle_length+m+2
    assert set(trace) == machine.rows and trace[0] == (0, 0)
    I = sum(a*3**j for j, a in enumerate(machine.encoded(word)))
    D = sum(a*3**j for j, (a, _) in enumerate(trace))
    A = sum(a*3**j for j, (_, a) in enumerate(trace))
    W, q = 3**m, 3**len(trace)
    assert D == I + W*A and 0 < I < W
    if not machine.binary:
        assert I % 2 == 0
    assert D > 0 and A > 0 and D+A < q
    assert m % 2 == len(trace) % 2 == 0
    F = {row: sum(3**j for j, edge in enumerate(trace) if edge == row)
         for row in machine.rows}
    if not machine.binary:
        G = F[0, 1] + F[1, 2]
        H = sum(F.values())
        assert G % 2 == H % 2 == 0 and H == (q-1)//2
    assert all(v > 0 for v in F.values())
    return dict(source_cells=len(word), binary_three_row=machine.binary, micro_width=m, cycles=cycles,
                micro_steps=len(trace), each_row_positive=True,
                even_width_and_time=True, scalar_joint_bound=True)


def check():
    systems = comparisons = accepts = zeros = max_states = 0
    graph_states = graph_edges = 0
    words = [word for n in range(1, 5) for word in product(range(2), repeat=n)]
    for choices in product(range(4), repeat=2):
        transitions = {(0, a): ((choice//2, choice % 2),)
                       for a, choice in enumerate(choices)}
        machine = Compiler(2, 2, {1}, transitions)
        ns, ne = machine.controller_graph()
        graph_states += ns
        graph_edges += ne
        for word in words:
            actual, size, zc = physical_reachable(machine, word)
            assert actual == source_reachable(machine, word), (choices, word)
            comparisons += 1
            accepts += actual
            zeros += zc
            max_states = max(max_states, size)
        systems += 1
    rng = random.Random(400102)
    for _ in range(32):
        transitions = {(s, a): tuple((t, b) for t in range(3) for b in range(2)
                                    if rng.randrange(4) == 0)
                       for s in range(2) for a in range(2)}
        machine = Compiler(2, 3, {2}, transitions)
        ns, ne = machine.controller_graph()
        graph_states += ns
        graph_edges += ne
        for word in words[:14]:
            actual, size, zc = physical_reachable(machine, word)
            assert actual == source_reachable(machine, word)
            comparisons += 1
            accepts += actual
            zeros += zc
            max_states = max(max_states, size)
        systems += 1
    binary_comparisons = 0
    for choices in product(range(4), repeat=2):
        transitions = {(0, a): ((choice//2, choice % 2),)
                       for a, choice in enumerate(choices)}
        machine = Compiler(2, 2, {1}, transitions, binary=True)
        machine.controller_graph()
        for word in words:
            actual, _, _ = physical_reachable(machine, word)
            assert actual == source_reachable(machine, word)
            binary_comparisons += 1
    traces = []
    for required in (1, 4, 9):
        transitions = {(s, a): ((min(required, s + int(a != 0)), a),)
                       for s in range(required) for a in range(2)}
        machine = Compiler(2, required+1, {required}, transitions)
        for word in ((1,), (0, 1), (1, 0, 1)):
            traces.append(deterministic_trace(machine, word))
        binary_machine = Compiler(2, required+1, {required}, transitions, binary=True)
        traces.append(deterministic_trace(binary_machine, (0, 1)))
    initially_halted = Compiler(2, 1, {0}, {})
    traces.append(deterministic_trace(initially_halted, (0,)))
    return dict(
        status='PASS_FOUR_ROW_FINITE_CONTROLLER_BLOCK_SIMULATOR',
        proof='four_row_queue_block_simulator.md',
        arithmetic_component='native_four_row_fifo66.md',
        physical_rows=sorted([list(row) for row in ROWS]),
        source_systems=systems, complete_graph_comparisons=comparisons,
        binary_three_row_comparisons=binary_comparisons,
        accepting_comparisons=accepts, verified_zero_queue_events=zeros,
        maximum_physical_states_seen=max_states,
        compiled_controller_states_total=graph_states,
        compiled_controller_edges_total=graph_edges,
        exact_trace_fixtures=traces,
        input_scope='Given valid block-coded source data, guard, and delimiter; '
                    'ordinary input loading is not supplied',
        controller_scope='Literal finite controller compiled without queue length; '
                         'arithmetic certification is not supplied',
        established_complete_bound=75,
    )


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = check()
    receipt = Path(__file__).with_suffix('.json')
    if args.write:
        receipt.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(receipt.read_text()) == result
    print(json.dumps(result, indent=2))
