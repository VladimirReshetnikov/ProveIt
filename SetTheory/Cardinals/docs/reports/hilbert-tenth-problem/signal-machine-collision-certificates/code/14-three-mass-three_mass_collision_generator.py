#!/usr/bin/env python3
"""Finite typed-channel, mass-three CA construction and finite validation.

Research prototype. No claim of a minimal alphabet or literal state=mass NCCA.
The mathematical construction is specified in three_mass_collision_lemma.md.
Only Python's standard library is used. Rule completion closes finite paths.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import product
from collections import defaultdict
import hashlib
import json


@dataclass(frozen=True)
class Instruction:
    source: str
    target: str
    operation: str   # inc, dec, nop, zero, positive
    counter: int = 0


class ThreeMassCA:
    D = 12
    K = 6
    CLOCK = 144

    def __init__(self, states, halt, instructions):
        self.states = tuple(states)
        self.halt = halt
        self.instructions = tuple(instructions)
        self.mod_i = len(instructions) + 1
        self.data = tuple(product(self.states, range(self.mod_i), range(self.K)))
        self.type_ids = {}
        self.names = []
        self.velocity = []
        self.single = {}
        self.pairs = {}
        self.pair_preimage = {}
        self.required_pair_count = 0
        self._build()
        self._complete_pairs()

    def typ(self, name, velocity=0):
        if name in self.type_ids:
            ident = self.type_ids[name]
            assert self.velocity[ident] == velocity
            return ident
        ident = len(self.names)
        self.type_ids[name] = ident
        self.names.append(name)
        self.velocity.append(velocity)
        self.single[ident] = ident
        return ident

    @staticmethod
    def pair(a, b):
        assert a != b
        return tuple(sorted((a, b)))

    def row(self, a, b, c, d):
        source, target = self.pair(a, b), self.pair(c, d)
        assert source not in self.pairs, ('duplicate domain', source)
        assert target not in self.pair_preimage, ('duplicate output', target)
        self.pairs[source] = target
        self.pair_preimage[target] = source

    def L(self, stage, data):
        return self.typ(('L', stage, data))

    def S(self, stage):
        return self.typ(('S', stage))

    def enabled(self, instr, residue):
        p = (2, 3)[instr.counter]
        divisible = residue % p == 0
        if instr.operation in ('dec', 'positive'):
            return divisible
        if instr.operation == 'zero':
            return not divisible
        return True

    def I(self, q, residue):
        choices = [j for j, ins in enumerate(self.instructions, 1)
                   if ins.source == q and self.enabled(ins, residue)]
        assert len(choices) <= 1, ('source is not deterministic', q, residue)
        return choices[0] if choices else 0

    def H(self, q, residue):
        choices = []
        for j, ins in enumerate(self.instructions, 1):
            if ins.target != q:
                continue
            # Morita's reversible syntax: only zero/positive tests can merge.
            if ins.operation in ('zero', 'positive') and not self.enabled(ins, residue):
                continue
            choices.append(j)
        assert len(choices) <= 1, ('source violates reversible syntax', q, residue)
        return choices[0] if choices else 0

    def gate(self, source_stage, target_stage, f):
        images = set()
        for x in self.data:
            y = f(x)
            assert y in self.data and y not in images
            images.add(y)
            self.row(self.L(source_stage, x), self.S(source_stage),
                     self.L(target_stage, y), self.S(target_stage))

    def query(self, label, source_stage, target_stage, epsilon, omit_halt=False):
        """z <- z + epsilon*(N mod 6), gap 12*N unchanged, 4*n+1 steps."""
        clock = {}
        for mode, direction, r in product(('P', 'M'), (1, -1), range(self.CLOCK)):
            clock[mode, direction, r] = self.typ(('clock', label, mode, direction, r), direction)
        for (mode, direction, r), t in clock.items():
            delta = 1 if mode == 'P' else -1
            self.single[t] = clock[mode, direction, (r + delta) % self.CLOCK]
        for r in range(self.CLOCK):
            self.row(self.R, clock['P', 1, r], self.R, clock['P', -1, (r + 1) % self.CLOCK])
            self.row(self.R, clock['M', 1, r], self.R, clock['M', -1, (r - 1) % self.CLOCK])
        for x in self.data:
            wp = self.typ(('wait', label, 'P', x))
            wm = self.typ(('wait', label, 'M', x))
            if not (omit_halt and x[0] == self.halt):
                self.row(self.L(source_stage, x), self.S(source_stage), wp, clock['P', 1, 1])
            self.row(wm, clock['M', -1, 0], self.L(target_stage, x), self.S(target_stage))
            for r in range(self.CLOCK):
                q, i, z = x
                h = r // (2 * self.D)
                y = (q, i, (z + epsilon * h) % self.K)
                wm_out = self.typ(('wait', label, 'M', y))
                self.row(wp, clock['P', -1, r], wm_out, clock['M', 1, (r - 1) % self.CLOCK])

    def arithmetic(self):
        escape = self.typ(('escape',), -1)
        for x in self.data:
            q, i, z = x
            if i == 0:
                trap = self.typ(('trap', x))
                self.row(self.L(4, x), self.S(4), trap, escape)
                continue
            ins = self.instructions[i - 1]
            prime = (2, 3)[ins.counter]
            if ins.operation not in ('inc', 'dec'):
                self.row(self.L(4, x), self.S(4), self.L(5, x), self.S(5))
                continue
            p, denominator = (prime, 1) if ins.operation == 'inc' else (1, prime)
            c, u = p + denominator, denominator - p
            right = self.typ(('arith', i, 1), c)
            left = self.typ(('arith', i, -1), -c)
            moving = self.typ(('moving', x), u)
            self.row(self.L(4, x), self.S(4), moving, right)
            self.row(moving, left, self.L(5, x), self.S(5))
        for i, ins in enumerate(self.instructions, 1):
            if ins.operation in ('inc', 'dec'):
                c = (2, 3)[ins.counter] + 1
                self.row(self.R, self.typ(('arith', i, 1), c),
                         self.R, self.typ(('arith', i, -1), -c))

    def _build(self):
        self.R = self.typ(('R',))
        for x, stage in product(self.data, range(8)):
            self.L(stage, x)
            self.S(stage)
        for q, residue in product(self.states, range(self.K)):
            self.I(q, residue)
            self.H(q, residue)
        self.query('forward-read', 0, 1, 1, omit_halt=True)
        self.gate(1, 2, lambda x: (x[0], (x[1] + self.I(x[0], x[2])) % self.mod_i, x[2]))
        self.query('forward-unread', 2, 3, -1)

        def change_state(x):
            q, i, z = x
            if i == 0:
                return x
            ins = self.instructions[i - 1]
            if q == ins.source:
                q = ins.target
            elif q == ins.target:
                q = ins.source
            return (q, i, z)

        self.gate(3, 4, change_state)
        self.arithmetic()
        self.query('backward-read', 5, 6, 1)
        self.gate(6, 7, lambda x: (x[0], (x[1] - self.H(x[0], x[2])) % self.mod_i, x[2]))
        self.query('backward-unread', 7, 0, -1)
        self.required_pair_count = len(self.pairs)
        assert len(set(self.single.values())) == len(self.single)
        assert all(self.velocity[a] == self.velocity[b] for a, b in self.single.items())

    def _complete_pairs(self):
        """Close every non-cyclic path of the finite partial pair injection."""
        starts = set(self.pairs) - set(self.pair_preimage)
        for start in sorted(starts):
            end = start
            while end in self.pairs:
                end = self.pairs[end]
            assert end not in self.pairs and start not in self.pair_preimage
            self.pairs[end] = start
            self.pair_preimage[start] = end
        assert set(self.pairs) == set(self.pair_preimage)
        assert len(set(self.pairs.values())) == len(self.pairs)

    def initial(self, q, N, i=0, z=0, stage=0):
        assert N >= 1
        return tuple(sorted(((-self.D * N, self.L(stage, (q, i, z))),
                             (-self.D * N, self.S(stage)), (0, self.R))))

    def step(self, particles, require_specified=False):
        cells = defaultdict(list)
        for position, typ in particles:
            cells[position].append(typ)
        result = []
        for position, present in cells.items():
            present = tuple(sorted(present))
            assert len(set(present)) == len(present), 'same channel collision'
            if len(present) == 1:
                out = (self.single[present[0]],)
            elif len(present) == 2:
                out = self.pairs.get(present, present)
                if require_specified:
                    assert present in self.specified_pairs, ('used completion row', present)
            else:
                assert not require_specified, 'unexpected triple collision'
                out = present
            result.extend((position + self.velocity[t], t) for t in out)
        assert len(result) == len(particles)
        assert len(set(result)) == len(result)
        return tuple(sorted(result))

    @property
    def specified_pairs(self):
        # Dict insertion order: the original rows precede completion rows.
        if not hasattr(self, '_specified_pairs'):
            self._specified_pairs = frozenset(list(self.pairs)[:self.required_pair_count])
        return self._specified_pairs

    def ready(self, particles):
        at = {t: position for position, t in particles}
        s = self.S(0)
        if s not in at:
            return None
        for position, typ in particles:
            name = self.names[typ]
            if name[0:2] == ('L', 0) and position == at[s]:
                q, i, z = name[2]
                if i == 0 and z == 0:
                    assert at[self.R] == 0
                    assert -position % self.D == 0
                    return q, -position // self.D
        return None

    def fingerprint(self):
        serial = {'types': self.names, 'velocity': self.velocity,
                  'singleton': sorted(self.single.items()), 'pairs': sorted(self.pairs.items()),
                  'required_pairs': self.required_pair_count}
        return hashlib.sha256(json.dumps(serial, sort_keys=True).encode()).hexdigest()


def run_tests():
    tests = []
    source = [Instruction('q0', 'q1', 'inc', 0), Instruction('q1', 'q2', 'inc', 1),
              Instruction('q2', 'q3', 'dec', 0), Instruction('q3', 'q0', 'dec', 1)]
    ca = ThreeMassCA(['q0', 'q1', 'q2', 'q3', 'halt'], 'halt', source)
    # Every run follows required rows only; the four instructions exercise every ratio.
    for N in (1, 2, 3, 6):
        conf = ca.initial('q0', N)
        expected = [('q1', 2*N), ('q2', 6*N), ('q3', 3*N), ('q0', N)]
        seen, times = [], []
        for tick in range(1, 20000*N):
            conf = ca.step(conf, require_specified=True)
            ready = ca.ready(conf)
            if ready is not None:
                seen.append(ready)
                times.append(tick)
                if len(seen) == 4:
                    break
        assert seen == expected, (N, seen)
        assert conf == ca.initial('q0', N)
        tests.append({'initial_N': N, 'ready_sequence': seen, 'ticks': times})
    # Query lemma: arbitrary finite scratch, every residue, exact boundary time.
    query_cases = 0
    for N, z, epsilon, stage, exit_stage in product(range(1, 7), (0, 3, 5), (1, -1), (0,), (1,)):
        if epsilon < 0:
            stage, exit_stage = 2, 3
        conf = ca.initial('q0', N, i=2, z=z, stage=stage)
        for _ in range(4*ca.D*N + 1):
            conf = ca.step(conf, require_specified=True)
        assert conf == ca.initial('q0', N, i=2, z=(z + epsilon*N) % 6, stage=exit_stage)
        query_cases += 1
    # Inverse merge: two test branches have the same target and distinct domain guards.
    merge_ca = ThreeMassCA(['zero_source', 'positive_source', 'halt'], 'halt',
                          [Instruction('zero_source', 'halt', 'zero', 0),
                           Instruction('positive_source', 'halt', 'positive', 0)])
    merge_tests = []
    for q, N in [('zero_source', 1), ('zero_source', 3), ('positive_source', 2), ('positive_source', 6)]:
        conf = merge_ca.initial(q, N)
        for tick in range(1, 10000*N):
            conf = merge_ca.step(conf, require_specified=True)
            if merge_ca.ready(conf) is not None:
                break
        assert merge_ca.ready(conf) == ('halt', N)
        # Completion must not freeze a newly reached ready-halt configuration.
        assert merge_ca.step(conf) != conf
        merge_tests.append({'source': q, 'N': N, 'committed_halt_tick': tick})
    # Invalid decrement is routed into an outgoing isolated escape, with no false halt.
    trap_ca = ThreeMassCA(['run', 'halt'], 'halt', [Instruction('run', 'halt', 'dec', 0)])
    conf = trap_ca.initial('run', 1)
    for tick in range(1, 1001):
        conf = trap_ca.step(conf, require_specified=True)
        assert trap_ca.ready(conf) != ('halt', 1)
    return {'status': 'passed', 'cycle_tests': tests, 'query_cases': query_cases,
            'inverse_merge_tests': merge_tests, 'trap_test_steps': 1000,
            'cycle_ca': {'types': len(ca.names), 'radius': max(map(abs, ca.velocity)),
                         'required_pairs': ca.required_pair_count,
                         'completed_pairs': len(ca.pairs), 'sha256': ca.fingerprint()},
            'merge_ca_sha256': merge_ca.fingerprint(), 'trap_ca_sha256': trap_ca.fingerprint()}


if __name__ == '__main__':
    print(json.dumps(run_tests(), indent=2))
