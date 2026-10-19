#!/usr/bin/env python3
"""Generate and check FC15/16 ground CNF with base-function congruence only.

New reduction: retain congruence for V,C. Reconstruct N,A,Q by their
incidence-profile contracts. W,Y,Z,H are existential witness constructors:
forget them before taking the equality quotient, then reconstruct them by
raw application to least-code representatives. The intermediate
five-base variant retains congruence for V,C,N,A,Q as a control.
Two further corollaries reconstruct the branch predicate G from the same
representative key and derive explicit Eq reflexivity from native row01
and left Euclidean equality. The proof is in skolem_reduct.tex.
No binary TM or state count is claimed.

The exact native payload, codec and original 29/30-clause comparison come
from ProveIt intake155/source44; byte-exact copies are in reference/.
The small quotient-certificate validator below adapts the representation in
ProveIt's finite_quotient_frontend.py but checks only the two assignment tags.
"""
from __future__ import annotations

import argparse
from collections import Counter
from contextlib import contextmanager
from dataclasses import dataclass
import hashlib
import itertools
import json
from pathlib import Path
import random
import sys
from types import ModuleType

HERE = Path(__file__).resolve().parent
BASE_FUNCTIONS = [('V', 2), ('C', 3), ('N', 2), ('A', 2), ('Q', 2)]
ALL_FUNCTIONS = BASE_FUNCTIONS + [('W', 3), ('Y', 3), ('Z', 3), ('H', 2)]
ASSIGNMENT_FUNCTIONS = BASE_FUNCTIONS[:2]
PROVEIT_PIN = '6446ff5668307a2ac6aee1896037f0b792090389'
EXPECTED_REFERENCES = {
    'LICENSE.ProveIt': '460d4fb6f45fd89278ba881d4b70e8bd1b7df223ee907e758342c2f9989f789d',
    'coded_extensional.py': '57d8f48de761b2a0ce0cd29f63935b729da84e5e185a263fff331eba7f5d74f8',
    'finite_class_closure.md': '2f60e5cb54f4ed11ab88489c85ed083513e3938c39fa888038588d3d36102ccc',
    'ground_kernel.py': '2ceebc265a6d2dc5d487f4b9d078a53d6b37d7718184e6f2c6da920b6a4985fb',
}


def require(p, message):
    if not p:
        raise ValueError(message)


@contextmanager
def reference_modules(path):
    names = ('ground_kernel', 'coded_extensional')
    previous = {n: sys.modules.get(n) for n in names}
    loaded = []
    try:
        for name in names:
            file = path / (name + '.py')
            m = ModuleType(name)
            m.__file__ = str(file)
            sys.modules[name] = m
            exec(compile(file.read_text(), str(file), 'exec'), m.__dict__)
            loaded.append(m)
        yield tuple(loaded)
    finally:
        for name, module in previous.items():
            if module is None:
                sys.modules.pop(name, None)
            else:
                sys.modules[name] = module


@dataclass(frozen=True)
class Stage:
    k: int
    clauses: tuple

    @property
    def B(self):
        return 1 << self.k

    @property
    def label_bits(self):
        return self.k * self.B

    @property
    def candidate_bits(self):
        return self.label_bits + 3 * self.B * self.B


class QuotientChecker:
    def __init__(self, kernel):
        self.K = kernel
        require(kernel.signature(False, True) == ALL_FUNCTIONS,
                'Native nine-function signature changed')

    def children(self, n):
        if n == 0:
            return None, ()
        tag, body = (n - 1) % 16, (n - 1) // 16
        arity = ALL_FUNCTIONS[tag][1] if tag < 9 else 1
        return tag, self.K.tuple_decode(body, arity)

    def function_constraints(self, B, retained=2):
        require(retained in (2, 5, 9), 'Expected assignment, five-base, or original congruence mode')
        for a in range(1, B):
            tag, args = self.children(a)
            if tag >= retained:
                continue
            for b in range(1, a):
                other, args2 = self.children(b)
                if tag == other:
                    yield a, b, tuple(zip(args, args2))

    def prepare(self, k, clauses):
        require(type(k) is int and k >= 0, 'Invalid stage')
        B = 1 << k
        out = tuple(tuple(row) for row in clauses)
        for row in out:
            for sign, pred, a, b in row:
                require(type(sign) is bool and type(pred) is int and 0 <= pred < 4,
                        'Malformed literal')
                require(type(a) is int and type(b) is int and 0 <= a < B and 0 <= b < B,
                        'Endpoint outside finite stage')
        return Stage(k, out)

    def prepare_native(self, k, native):
        B = 1 << k
        out = []
        for row in native:
            variables = self.K.clause_variables(row)
            for values in itertools.product(range(B), repeat=len(variables)):
                env = dict(zip(variables, values))
                ground = tuple((sign, self.K.PREDICATES.index(pred),
                    self.K.ground_term(a, env, False, True),
                    self.K.ground_term(b, env, False, True))
                    for sign, pred, a, b in row)
                if all(a < B and b < B for _, _, a, b in ground):
                    out.append(ground)
        return self.prepare(k, out)

    @staticmethod
    def labels(stage, candidate):
        return tuple((candidate >> (stage.k * i)) & (stage.B - 1)
                     for i in range(stage.B))

    def function_valid(self, labels, retained=2):
        return all(not all(labels[x] == labels[y] for x, y in args)
                   or labels[a] == labels[b]
                   for a, b, args in self.function_constraints(len(labels), retained))

    def valid(self, stage, candidate, retained=2, raw_guard=False):
        require(type(candidate) is int and 0 <= candidate < 1 << stage.candidate_bits,
                'Candidate outside exact finite range')
        labels = self.labels(stage, candidate)
        if not self.function_valid(labels, retained):
            return False
        def truth(literal):
            sign, pred, a, b = literal
            x, y = (a, b) if raw_guard and pred == 2 else (labels[a], labels[b])
            value = (x == y) if pred == 3 else bool((candidate >>
                (stage.label_bits + pred + 3 * (stage.B * x + y))) & 1)
            return value == sign
        return all(any(truth(l) for l in row) for row in stage.clauses)

    def decide(self, stage, raw_guard=False):
        # No timeout or resource error is converted to mathematical UNSAT.
        for candidate in range(1 << stage.candidate_bits):
            if self.valid(stage, candidate, raw_guard=raw_guard):
                return {'status': 'SAT', 'witness': candidate,
                        'candidates_checked': candidate + 1}
        return {'status': 'UNSAT', 'witness': None,
                'candidates_checked': 1 << stage.candidate_bits}


def independent_function_valid(K, labels, names):
    """Comparison uses fully decoded trees, independent of tag-pair loops."""
    trees = {n: K.decode(n, False, True) for n in range(1, len(labels))}
    outputs = {}
    for n, tree in trees.items():
        if tree[0] not in names:
            continue
        key = (tree[0], tuple(labels[K.encode(t, False, True)] for t in tree[1:]))
        if key in outputs and outputs[key] != labels[n]:
            return False
        outputs[key] = labels[n]
    return True


def run(reference, output):
    output.mkdir(parents=True, exist_ok=True)
    observed_refs = {name: hashlib.sha256((reference / name).read_bytes()).hexdigest()
                     for name in EXPECTED_REFERENCES}
    require(observed_refs == EXPECTED_REFERENCES, 'Pinned reference input digest changed')
    report = {'status': 'PASS',
        'scope': 'Exact finite theory/encoding reduction and certificate controls; no binary machine theorem',
        'proveit_commit': PROVEIT_PIN,
        'reference_sha256': observed_refs,
        'retained_congruence_functions': ASSIGNMENT_FUNCTIONS,
        'reconstructed_profile_functions': BASE_FUNCTIONS[2:],
        'witness_functions_forgotten_then_reconstructed': ALL_FUNCTIONS[5:], 'theories': {}}
    with reference_modules(reference) as (K, C):
        require(K.signature(False, True) == ALL_FUNCTIONS, 'Unexpected source signature')
        equality_full = K.equality_clauses(False, ALL_FUNCTIONS)
        equality_weak = K.equality_clauses(False, ASSIGNMENT_FUNCTIONS)
        equality_intermediate = K.equality_clauses(False, BASE_FUNCTIONS)
        require(len(equality_full) == 14 and len(equality_weak) == 7
                and len(equality_intermediate) == 10, 'Equality row count changed')
        require(equality_weak[0] == [K.Eq('x', 'x')], 'Reflexivity source row changed')
        require({pred for _, pred, *_ in equality_weak[-1]} == {'Eq', 'G'},
                'Final equality row is not G transport')
        equality_raw_guard = equality_weak[:-1]
        equality_minimal = equality_raw_guard[1:]
        all_native = {'fc15': K.source_clauses(False, True), 'fc16': C.native_clauses()}
        for name, native in all_native.items():
            full, weak = native + equality_full, native + equality_weak
            original_bits = K.payload_bits(full, False, ALL_FUNCTIONS)
            bits = K.payload_bits(weak, False, ALL_FUNCTIONS)
            require(C._read_stream(bits) == C._canonical(weak), 'Independent payload decoder disagrees')
            stem = name + '_assignment_congruence'
            (output / (stem + '.bits')).write_text(bits + '\n')
            (output / (stem + '.json')).write_text(json.dumps(weak, indent=2) + '\n')
            # Binary file uses an explicitly specified trailing-zero padding.
            padding = (-len(bits)) % 8
            packed = int(bits + '0' * padding, 2).to_bytes((len(bits) + padding) // 8, 'big')
            (output / (stem + '.bin')).write_bytes(packed)
            intermediate = native + equality_intermediate
            intermediate_bits = K.payload_bits(intermediate, False, ALL_FUNCTIONS)
            (output / (name + '_five_base_congruence.bits')).write_text(intermediate_bits + '\n')
            require(C._read_stream(intermediate_bits) == C._canonical(intermediate),
                    'Intermediate decoder roundtrip failed')
            m = {'original': K.metrics(full, functions=ALL_FUNCTIONS),
                 'five_base_control': K.metrics(intermediate, functions=ALL_FUNCTIONS),
                 'assignment_congruence': K.metrics(weak, functions=ALL_FUNCTIONS),
                 'saved_bits': len(original_bits) - len(bits),
                 'packed_bytes': len(packed), 'trailing_zero_padding_bits': padding,
                 'payload_sha256': hashlib.sha256(bits.encode()).hexdigest(),
                 'independent_roundtrip': True}
            require(m['saved_bits'] == 421, 'Expected exact 421-bit reduction')
            require(m['original']['literals'] - m['assignment_congruence']['literals'] == 24,
                    'Expected exact 24-literal reduction')
            m['additional_corollaries'] = {}
            for variant, completion, expected_bits in (
                ('raw_guard', equality_raw_guard, 1148 if name == 'fc15' else 1355),
                ('raw_guard_derived_reflexivity', equality_minimal,
                 1134 if name == 'fc15' else 1341)):
                variant_clauses = native + completion
                variant_bits = K.payload_bits(variant_clauses, False, ALL_FUNCTIONS)
                require(C._read_stream(variant_bits) == C._canonical(variant_clauses),
                        'Corollary payload independent decoder disagrees')
                require(len(variant_bits) == expected_bits, 'Corollary bit count changed')
                variant_stem = name + '_' + variant
                (output / (variant_stem + '.bits')).write_text(variant_bits + '\n')
                (output / (variant_stem + '.json')).write_text(json.dumps(variant_clauses, indent=2) + '\n')
                variant_padding = (-len(variant_bits)) % 8
                variant_packed = int(variant_bits + '0' * variant_padding, 2).to_bytes(
                    (len(variant_bits) + variant_padding) // 8, 'big')
                (output / (variant_stem + '.bin')).write_bytes(variant_packed)
                m['additional_corollaries'][variant] = {
                    'metrics': K.metrics(variant_clauses, functions=ALL_FUNCTIONS),
                    'saved_bits_vs_original': len(original_bits) - len(variant_bits),
                    'packed_bytes': len(variant_packed),
                    'trailing_zero_padding_bits': variant_padding,
                    'payload_sha256': hashlib.sha256(variant_bits.encode()).hexdigest(),
                    'independent_roundtrip': True,
                }
            report['theories'][name] = m

        checker = QuotientChecker(K)
        controls = []
        # The same-argument witness values may differ on an Eq-class.  These
        # controls are local finite certificates, never full FC15 models.
        stage = checker.prepare(5, [])
        labels = [0] * 32
        labels[22] = 1             # W(0,0,0)=code6, W(1,0,0)=code22.
        candidate = sum(label << (5 * i) for i, label in enumerate(labels))
        require(checker.valid(stage, candidate), 'Assignment mode rejected noncongruent witness')
        require(checker.valid(stage, candidate, 5), 'Five-base mode rejected noncongruent witness')
        require(not checker.valid(stage, candidate, 9), 'Original mode must reject witness noncongruence')
        controls.append({'name': 'Skolem_W_may_split_an_equality_class', 'status': 'PASS',
                         'B': 32, 'labels_nonzero': {'22': 1},
                         'assignment_accepts': True, 'five_base_accepts': True, 'all_nine_accepts': False,
                         'scope': 'Empty-native finite control, not a full theory model'})
        labels = [0] * 32
        labels[17] = 1             # V(0,0)=code1, V(1,0)=code17.
        require(not checker.function_valid(labels), 'Base V congruence was accidentally omitted')
        controls.append({'name': 'base_V_congruence_remains_required', 'status': 'PASS',
                         'B': 32, 'labels_nonzero': {'17': 1}, 'assignment_accepts': False})
        labels = [0] * 32
        labels[19] = 1             # N is reconstructed from incidence profiles.
        require(checker.function_valid(labels), 'Assignment mode must permit N noncongruence')
        require(not checker.function_valid(labels, 5), 'Five-base control must reject N noncongruence')
        controls.append({'name': 'profile_constructor_N_may_split_an_equality_class',
                         'status': 'PASS', 'B': 32, 'labels_nonzero': {'19': 1},
                         'assignment_accepts': True, 'five_base_accepts': False,
                         'scope': 'Empty-native finite control, not a full theory model'})

        guard_stage = checker.prepare(1, [[(True, 2, 0, 0)], [(False, 2, 1, 0)]])
        guard_candidate = 1 << (guard_stage.label_bits + 2)
        require(checker.valid(guard_stage, guard_candidate, raw_guard=True),
                'Raw guard must permit different G values on one Eq class')
        require(not checker.valid(guard_stage, guard_candidate),
                'Class-indexed guard must reject the guard-splitting fixture')
        # Decode the raw guard table independently into an explicit dictionary.
        raw_guard_table = {(a, b): bool(guard_candidate & (1 <<
                           (guard_stage.label_bits + 2 + 3 * (guard_stage.B * a + b))))
                           for a in range(guard_stage.B) for b in range(guard_stage.B)}
        require(raw_guard_table[(0, 0)] and not raw_guard_table[(1, 0)],
                'Independent raw guard fixture decode disagrees')
        controls.append({'name': 'G_can_split_an_equality_class', 'status': 'PASS',
                         'B': 2, 'candidate': guard_candidate,
                         'raw_guard_accepts': True, 'class_guard_accepts': False,
                         'scope': 'Two-literal local guard fixture, not a full theory model'})
        for pred in (0, 1):
            predicate_stage = checker.prepare(1, [[(True, pred, 0, 0)], [(False, pred, 1, 0)]])
            predicate_candidate = 1 << (predicate_stage.label_bits + pred)
            require(not checker.valid(predicate_stage, predicate_candidate, raw_guard=True),
                    'Raw guard mode accidentally weakened E or Inc congruence')
        report['raw_guard_preserves_E_and_Inc_transport_controls'] = 2

        rng = random.Random(245251351)
        comparisons = 0
        for B in (2, 4, 8, 16, 32, 64):
            for _ in range(80):
                labels = [rng.randrange(min(4, B)) for i in range(B)]
                for count in (2, 5, 9):
                    a = checker.function_valid(labels, count)
                    b = independent_function_valid(K, labels, {n for n, _ in ALL_FUNCTIONS[:count]})
                    require(a == b, 'Arithmetic and full-tree congruence checks disagree')
                    comparisons += 1
        report['controls'] = controls
        report['independent_function_comparisons'] = comparisons
        report['native_small_stages'] = {
            name: [{'k': k, 'kept_native_instances': len((stage := checker.prepare_native(k, native)).clauses),
                    **checker.decide(stage)} for k in (0, 1)]
            for name, native in all_native.items()}
        report['native_k2_witnesses'] = {}
        for name, native in all_native.items():
            stage = checker.prepare_native(2, native)
            witness = 2097728
            require(len(stage.clauses) > 0, 'Expected non-vacuous native k2 stage')
            require(checker.valid(stage, witness), 'Inherited native k2 witness rejected')
            require(checker.valid(stage, witness, 9), 'Inherited witness fails original completion')
            require(checker.valid(stage, witness, raw_guard=True), 'Raw guard mode rejects native k2 witness')
            require(not checker.valid(stage, 0), 'Expected zero candidate to fail a native k2 clause')
            report['native_k2_witnesses'][name] = {
                'k': 2, 'B': stage.B, 'candidate_bits': stage.candidate_bits,
                'kept_native_instances': len(stage.clauses), 'witness': witness,
                'assignment_accepts': True, 'all_nine_accepts': True,
                'raw_guard_accepts': True,
                'zero_candidate_rejected': True,
                'scope': 'Explicit native-stage SAT witness, no exhaustive k2 search',
            }
        report['whole_signature_pair_counts'] = {
            str(B): {'assignment': sum(1 for _ in checker.function_constraints(B, 2)),
                     'five_base': sum(1 for _ in checker.function_constraints(B, 5)),
                     'all_nine': sum(1 for _ in checker.function_constraints(B, 9))}
            for B in (16, 32, 64, 128)}
        # Guard against mistaking the six closure CNF clauses for Horn rules.
        native = all_native['fc15']
        report['native_non_horn_rows'] = [i + 1 for i, row in enumerate(native)
                                        if sum(sign for sign, *_ in row) > 1]
        require(report['native_non_horn_rows'], 'Unexpected Horn simplification')
    (output / 'results.json').write_text(json.dumps(report, indent=2) + '\n')
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reference', type=Path, default=HERE / 'reference')
    parser.add_argument('--output', type=Path, default=HERE / 'skolem_reduct_results')
    args = parser.parse_args()
    result = run(args.reference, args.output)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
