#!/usr/bin/env python3
"""Exact finite quotient stages for intake155/source44 FC15* and FC16*.

Default: recover the unchanged source44 package through reproduce_155.py
--prepare-only, then run practical finite checks. --package selects an already
recovered copy. --run-stage K explicitly requests an unrestricted finite
decision; even modest K can take impractical time. Errors are never UNSAT.
No binary compiler, state bound, Lean build or PA formalization is supplied.
"""
from __future__ import annotations

import argparse
from contextlib import contextmanager
from dataclasses import dataclass
import itertools
import json
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import time
from types import ModuleType

ROOT = Path(__file__).resolve().parents[4]
HOST = ROOT / 'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels'
ARRIVAL = 'fab89c5d26b81cd2ccab2ee5d213ff23725c7726'
ARCHIVE = 'docs/incoming/zfc_finite_closure_2026-10-17.zip'
WRAPPER = 'zfc_finite_closure'


def require(condition, message):
    if not condition:
        raise ValueError(message)


@contextmanager
def source_modules(package):
    """Load two audited modules from an explicit copy, without bytecode writes."""
    previous = {name: sys.modules.get(name)
                for name in ('ground_kernel', 'coded_extensional')}
    modules = []
    try:
        for name in previous:
            path = package / 'code' / (name + '.py')
            module = ModuleType(name)
            module.__file__ = str(path)
            sys.modules[name] = module
            exec(compile(path.read_text(), str(path), 'exec'), module.__dict__)
            modules.append(module)
        yield modules
    finally:
        for name, module in previous.items():
            if module is None:
                sys.modules.pop(name, None)
            else:
                sys.modules[name] = module


@dataclass(frozen=True)
class Stage:
    k: int
    clauses: tuple[tuple[tuple[bool, int, int, int], ...], ...]
    theory: str
    instances_considered: int

    @property
    def B(self):
        return 1 << self.k

    @property
    def label_bits(self):
        return self.k * self.B

    @property
    def candidate_bits(self):
        return self.label_bits + 3 * self.B * self.B


class Frontend:
    def __init__(self, kernel, coded, package):
        self.K, self.C = kernel, coded
        self.functions = kernel.signature(False, True)
        require(self.functions == [('V', 2), ('C', 3), ('N', 2), ('A', 2),
                                  ('Q', 2), ('W', 3), ('Y', 3), ('Z', 3),
                                  ('H', 2)], 'Source44 retained signature changed')
        require(kernel.RADIX == 16, 'Source44 term radix changed')
        self.payloads = {}
        for theory, filename in [('fc15', 'fc15_derived_member.bits'),
                                 ('fc16', 'fc16_coded_extensional.bits')]:
            rows = self.native(theory)
            completed = rows + kernel.equality_clauses(False, self.functions)
            bits = kernel.payload_bits(completed, False, self.functions)
            require(bits == (package / 'data' / filename).read_text().strip(),
                    'Exact complete clause stream changed: ' + theory)
            self.payloads[theory] = dict(
                native_clauses=len(rows), completed_clauses=len(completed),
                max_native_variables=max(len(kernel.clause_variables(row))
                                         for row in rows),
                max_completed_variables=max(len(kernel.clause_variables(row))
                                            for row in completed),
                native_bits=len(kernel.payload_bits(rows, False, self.functions)),
                completed_bits=len(bits))

    def native(self, theory):
        require(theory in {'fc15', 'fc16'}, 'Expected fc15 or fc16')
        return (self.K.source_clauses(False, True) if theory == 'fc15'
                else self.C.native_clauses())

    def children(self, n):
        if n == 0:
            return None, ()
        tag, payload = (n - 1) % 16, (n - 1) // 16
        arity = self.functions[tag][1] if tag < 9 else 1
        return tag, self.K.tuple_decode(payload, arity)

    def function_constraints(self, B):
        """Each result denotes equal argument labels => equal output labels."""
        for a in range(1, B):
            tag, args = self.children(a)
            if tag >= 9:
                continue
            for b in range(1, a):
                other_tag, other_args = self.children(b)
                if tag == other_tag:
                    yield a, b, tuple(zip(args, other_args))

    def prepare_cnf(self, k, clauses, theory='control', considered=0):
        """Adapt legacy signed atom codes for controls, outside the checker."""
        require(type(k) is int and k >= 0, 'k must be a nonnegative integer')
        direct = []
        for row in clauses:
            converted = []
            for literal in row:
                require(type(literal) is int and literal != 0,
                        'Expected a nonzero signed ground atom')
                atom = abs(literal) - 1
                a, b = self.K.unpair(atom // 4)
                converted.append((literal > 0, atom % 4, a, b))
            direct.append(converted)
        return self.prepare_literals(k, direct, theory, considered)

    def prepare_literals(self, k, clauses, theory='control', considered=0):
        """Actual evaluator input: sign/predicate/endpoint quadruples."""
        require(type(k) is int and k >= 0, 'k must be a nonnegative integer')
        B = 1 << k
        clauses = tuple(tuple(row) for row in clauses)
        for row in clauses:
            for sign, pred, a, b in row:
                require(type(sign) is bool and type(pred) is int and 0 <= pred < 4,
                        'Malformed sign or predicate tag')
                require(type(a) is int and type(b) is int and
                        0 <= a < B and 0 <= b < B,
                        'Ground atom lies outside the stage carrier')
        return Stage(k, clauses, theory, considered)

    def to_cnf(self, stage):
        """Diagnostic conversion only; the decision engine never calls it."""
        return tuple(tuple((1 if sign else -1) *
                           (1 + pred + 4 * self.K.pair(a, b))
                           for sign, pred, a, b in row)
                     for row in stage.clauses)

    def prepare_stage(self, k, theory='fc15'):
        require(type(k) is int and k >= 0, 'k must be a nonnegative integer')
        B = 1 << k
        inside, considered = [], 0
        for row in self.native(theory):
            variables = self.K.clause_variables(row)
            for values in itertools.product(range(B), repeat=len(variables)):
                considered += 1
                env = dict(zip(variables, values))
                ground = tuple((sign, self.K.PREDICATES.index(pred),
                                self.K.ground_term(a, env, False, True),
                                self.K.ground_term(b, env, False, True))
                               for sign, pred, a, b in row)
                if all(a < B and b < B for _, _, a, b in ground):
                    inside.append(ground)
        return self.prepare_literals(k, inside, theory, considered)

    @staticmethod
    def label(stage, candidate, i):
        return (candidate >> (stage.k * i)) & (stage.B - 1)

    def valid(self, stage, candidate):
        """Pure certificate checker: one integer, no SAT solver or fuel."""
        require(type(candidate) is int and
                0 <= candidate < (1 << stage.candidate_bits),
                'Candidate lies outside the exact finite range')
        label = lambda i: self.label(stage, candidate, i)
        for a, b, args in self.function_constraints(stage.B):
            if all(label(x) == label(y) for x, y in args) and label(a) != label(b):
                return False

        def literal_value(literal):
            sign, pred, a, b = literal
            x, y = label(a), label(b)
            if pred == 3:
                value = x == y
            else:
                position = stage.label_bits + pred + 3 * (stage.B * x + y)
                value = bool((candidate >> position) & 1)
            return value == sign

        return all(any(literal_value(literal) for literal in row)
                   for row in stage.clauses)

    def decide(self, stage):
        """Complete finite decision. UNSAT occurs only after the whole range.

        There is intentionally no fuel, timeout, catch-all exception handler,
        or approximation. A host failure propagates instead of returning UNSAT.
        """
        for candidate in range(1 << stage.candidate_bits):
            if self.valid(stage, candidate):
                return dict(status='SAT', satisfiable=True, witness=candidate,
                            candidates_checked=candidate + 1,
                            candidate_bits=stage.candidate_bits)
        return dict(status='UNSAT', satisfiable=False, witness=None,
                    candidates_checked=1 << stage.candidate_bits,
                    candidate_bits=stage.candidate_bits)

    def stage_exists(self, k, theory='fc15'):
        """Exact SAT(G_(2^k)); this unrestricted API may be impractical."""
        return self.decide(self.prepare_stage(k, theory))['satisfiable']

    def explicit_equality_cnf(self, B, include_predicates=True):
        """Independent expanded local congruence baseline for finite tests."""
        e = lambda a, b: 1 + 3 + 4 * self.K.pair(a, b)
        rows = [(e(x, x),) for x in range(B)]
        rows += [(-e(x, y), -e(x, z), e(y, z))
                 for x, y, z in itertools.product(range(B), repeat=3)]
        # Independently use full decoded trees and their retained names here,
        # rather than the checker's arithmetic tag/argument matcher.
        trees = {n: self.K.decode(n, False, True) for n in range(1, B)}
        retained = {name for name, _ in self.functions}
        for a, tree in trees.items():
            if tree[0] not in retained:
                continue
            for b, other in trees.items():
                if b < a and tree[0] == other[0]:
                    args = zip(tree[1:], other[1:])
                    rows.append(tuple(-e(self.K.encode(x, False, True),
                                         self.K.encode(y, False, True))
                                      for x, y in args) + (e(a, b),))
        if include_predicates:
            for p in range(3):
                for x, y, u, v in itertools.product(range(B), repeat=4):
                    rows.append((-e(x, y), -e(u, v),
                                 -(1 + p + 4 * self.K.pair(x, u)),
                                 1 + p + 4 * self.K.pair(y, v)))
        return rows

    def induced(self, stage, candidate):
        labels = [self.label(stage, candidate, i) for i in range(stage.B)]
        bits = candidate >> stage.label_bits
        return {1 + p + 4 * self.K.pair(a, b):
                (labels[a] == labels[b] if p == 3 else
                 bool(bits >> (p + 3 * (stage.B * labels[a] + labels[b])) & 1))
                for p, a, b in itertools.product(range(4), range(stage.B),
                                                range(stage.B))}


def finite_checks(frontend):
    K = frontend.K
    start = time.monotonic()
    stages, tiny_decisions = [], []
    for theory in ('fc15', 'fc16'):
        for k in (0, 1, 2):
            stage = frontend.prepare_stage(k, theory)
            B = stage.B
            baseline = tuple(row for row in K.instances(
                frontend.native(theory), B - 1, False, True)
                if all(max(K.unpair((abs(l) - 1) // 4)) < B for l in row))
            require(frontend.to_cnf(stage) == baseline,
                    'Direct endpoint clauses differ from delivered instantiator')
            row = dict(theory=theory, k=k, B=B,
                       native_instances_considered=stage.instances_considered,
                       native_instances_inside=len(stage.clauses),
                       candidate_bits=stage.candidate_bits,
                       old_equality_instances=sum(
                           B ** len(K.clause_variables(c))
                           for c in K.equality_clauses(False, frontend.functions)),
                       function_pair_loop_bound=B * (B - 1) // 2,
                       matching_function_pairs=sum(
                           1 for _ in frontend.function_constraints(B)))
            stages.append(row)
            if k < 2:
                decision = frontend.decide(stage)
                require(decision['satisfiable'], 'Unexpected tiny native UNSAT')
                require(frontend.stage_exists(k, theory) == decision['satisfiable'],
                        'Public stage_exists API differs')
                tiny_decisions.append(dict(theory=theory, k=k, **decision))

    # A nontrivial native stage certificate: class(0,1,2)=0, class(3)=1;
    # Inc(s,d) is true and Inc(s,N(d,d)) is false for both represented classes.
    native_witnesses = []
    for theory in ('fc15', 'fc16'):
        stage = frontend.prepare_stage(2, theory)
        witness = (1 << 6) + (1 << 9) + (1 << 21)
        require(frontend.valid(stage, witness), 'Native k2 witness changed')
        require(K.valuation_satisfies(
            frontend.to_cnf(stage) + tuple(frontend.explicit_equality_cnf(4)),
            frontend.induced(stage, witness)), 'Native witness expansion differs')
        native_witnesses.append(dict(theory=theory, k=2, witness=witness,
                                     native_ground_clauses=len(stage.clauses),
                                     full_candidate_enumeration_run=False))

    random_checks = 0
    rng = random.Random(15544)
    for k in (0, 1, 2, 3, 5):
        stage = frontend.prepare_cnf(k, [])
        eq = frontend.explicit_equality_cnf(stage.B, k <= 3)
        for _ in range(60):
            candidate = rng.getrandbits(stage.candidate_bits)
            require(frontend.valid(stage, candidate) ==
                    K.valuation_satisfies(eq, frontend.induced(stage, candidate)),
                    'Partition and explicit congruence valuation differ')
            random_checks += 1
        for n in range(stage.B):
            require(all(child < n for child in frontend.children(n)[1]),
                    'Term child is not smaller')
            require(K.encode(K.decode(n, False, True), False, True) == n,
                    'Total term roundtrip failed')

    # Recover every congruent relational valuation on a two-element carrier.
    stage = frontend.prepare_cnf(1, [])
    eq_rows = frontend.explicit_equality_cnf(2)
    reverse_checked = 0
    for eqbits in range(16):
        e = lambda a, b: bool(eqbits >> (2 * a + b) & 1)
        if not all(e(x, x) for x in range(2)):
            continue
        if not all(not (e(x, y) and e(x, z)) or e(y, z)
                   for x, y, z in itertools.product(range(2), repeat=3)):
            continue
        labels = [min(y for y in range(2) if e(x, y)) for x in range(2)]
        U = sum(label << i for i, label in enumerate(labels))
        for V in range(1 << 12):
            value = {1 + p + 4 * K.pair(a, b):
                     (e(a, b) if p == 3 else bool(V >> (p + 3 * (2 * a + b)) & 1))
                     for p, a, b in itertools.product(range(4), range(2), range(2))}
            if K.valuation_satisfies(eq_rows, value):
                require(frontend.induced(stage, U + (V << 2)) == value,
                        'Congruent valuation not recovered')
                reverse_checked += 1

    eq = lambda a, b: 1 + 3 + 4 * K.pair(a, b)
    pred = lambda a, b: 1 + 4 * K.pair(a, b)
    fixtures = [([], True),
                ([(eq(0, 1),), (pred(0, 0),), (-pred(1, 0),)], False),
                ([(eq(0, 1),), (-eq(0, 1),)], False),
                ([(-eq(0, 1),)], True),
                ([()], False)]
    decisions = []
    for clauses, expected in fixtures:
        decision = frontend.decide(frontend.prepare_cnf(1, clauses))
        require(decision['satisfiable'] == expected, 'Fixture decision changed')
        decisions.append(decision)
    require(all(d['candidates_checked'] == 16384
                for d in decisions if not d['satisfiable']),
            'UNSAT control did not exhaust every candidate')

    invalid_calls = [lambda: frontend.prepare_cnf(-1, []),
                     lambda: frontend.prepare_cnf(True, []),
                     lambda: frontend.prepare_cnf(1, [(0,)]),
                     lambda: frontend.prepare_cnf(1, [(eq(0, 2),)]),
                     lambda: frontend.valid(stage, -1),
                     lambda: frontend.valid(stage, True),
                     lambda: frontend.valid(stage, 1 << stage.candidate_bits)]
    for call in invalid_calls:
        try:
            call()
        except ValueError:
            pass
        else:
            raise ValueError('Malformed input was accepted')

    # Resource exceptions must remain exceptions rather than being called UNSAT.
    original = frontend.valid
    def fail(*_args):
        raise MemoryError('deliberate finite-test resource failure')
    try:
        frontend.valid = fail
        try:
            frontend.decide(stage)
        except MemoryError:
            pass
        else:
            raise ValueError('Resource error was converted into a decision')
    finally:
        frontend.valid = original

    stage32 = frontend.prepare_cnf(5, [])
    require(frontend.children(1) == (0, (0, 0)) and
            frontend.children(17) == (0, (1, 0)), 'V control codes changed')
    invalid = 1 << (5 * 17)
    require(not frontend.valid(stage32, invalid),
            'Required retained-function congruence was omitted')
    require(frontend.children(10) == (9, (0,)) and
            frontend.children(26) == (9, (1,)), 'Padding control codes changed')
    require(frontend.valid(stage32, 1 << (5 * 26)),
            'Unneeded padding-function congruence was added')

    alignment = []
    for theory in ('fc15', 'fc16'):
        ground = list(K.instances(frontend.native(theory), 0, False, True))
        maximum = max(x for row in ground for l in row
                      for x in K.unpair((abs(l) - 1) // 4))
        alignment.append(dict(theory=theory, delivered_stage0_max_term=maximum,
                              first_covering_k=maximum.bit_length()))
    return dict(status='PASS', seconds=time.monotonic() - start,
                payloads=frontend.payloads, stages=stages,
                native_tiny_stage_decisions=tiny_decisions,
                native_k2_witnesses=native_witnesses,
                random_partition_checks=random_checks,
                complete_two_element_valuations_recovered=reverse_checked,
                exhaustive_fixture_decisions=decisions,
                malformed_inputs_rejected=len(invalid_calls),
                resource_error_propagation=True,
                retained_function_omission_rejected=True,
                padding_noncongruence_accepted=True, stage_alignment=alignment)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--package', type=Path,
                        help='source44 wrapper from batch155 prepare-only')
    parser.add_argument('--output', type=Path)
    parser.add_argument('--run-stage', type=int,
                        help='explicit unrestricted stage; no fuel or timeout')
    parser.add_argument('--theory', choices=('fc15', 'fc16'), default='fc15')
    args = parser.parse_args()
    if args.run_stage is not None and args.run_stage < 0:
        parser.error('--run-stage must be nonnegative')
    with tempfile.TemporaryDirectory(prefix='zfc-finite-quotient-') as scratch:
        if args.package:
            package = args.package.resolve()
        else:
            subprocess.run([sys.executable, '-B', str(HOST / 'code/reproduce_155.py'),
                            '--prepare-only', '--output', scratch], check=True)
            package = Path(scratch) / '44' / WRAPPER
        if args.output and args.output.resolve().is_relative_to(package):
            parser.error('Place result JSON outside the recovered package')
        with source_modules(package) as (kernel, coded):
            frontend = Frontend(kernel, coded, package)
            result = finite_checks(frontend)
            if args.run_stage is not None:
                stage = frontend.prepare_stage(args.run_stage, args.theory)
                print(f'Explicit decision: {args.theory}, k={stage.k}, '
                      f'{stage.candidate_bits} candidate bits; no cutoff.',
                      file=sys.stderr, flush=True)
                result['requested_stage'] = dict(
                    theory=args.theory, k=stage.k, **frontend.decide(stage))
    result.update(arrival=ARRIVAL, archive=ARCHIVE, wrapper=WRAPPER,
                  source_proveit_pin='61e77836565f63582561f54745f633d50efd9c7d',
                  python_version=sys.version,
                  source_mode='explicit recovered copy' if args.package else
                  'offline git recovery through batch155 prepare-only',
                  checker_interface='prepared stage plus one packed candidate integer',
                  literal_interface='sign, predicate tag, left term code, right term code',
                  runtime_atom_pairing=False,
                  UNSAT_requires_complete_candidate_exhaustion=True,
                  scope='Exact finite stage checker and practical tests; ordinary '
                  'unbounded equivalence is documented separately. No binary '
                  'compiler, state bound, Lean proof or PA theorem.',
                  Lean_built=False, Coq_built=False)
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
