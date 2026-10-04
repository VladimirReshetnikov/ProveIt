#!/usr/bin/env python3
"""Independent finite-polynomial audit; never imports or executes packet code.

Sparse monomials are sorted tuples of variable names (not exponent vectors).
The only exhaustive search is finite polynomial satisfiability after algebraic
elimination. It examines all candidate edge words, including disconnected and
guard-invalid words; it is not a native-machine or physical interpreter.
"""
from collections import Counter
from dataclasses import dataclass
from itertools import product
from pathlib import Path
import argparse
import hashlib
import json
import os

HERE = Path(__file__).resolve().parent
EXPECTED_PROOF = '5d9d7de3c9b6ca5551d7cd537b0e3570c0272af6716ba814453d5ad2123aea6a'
EXPECTED_MANIFEST = '54d8abdcc872f628e9ae6639f4119b15cd1d4bacd33ba412ffd85155110b3824'


class Poly:
    def __init__(self, terms):
        self.terms = {m: c for m, c in terms.items() if c}

    @staticmethod
    def cast(value):
        return value if isinstance(value, Poly) else Poly({(): value})

    def __add__(self, rhs):
        result = Counter(self.terms)
        result.update(self.cast(rhs).terms)
        return Poly(dict(result))

    __radd__ = __add__

    def __neg__(self):
        return Poly({m: -c for m, c in self.terms.items()})

    def __sub__(self, rhs):
        return self + -self.cast(rhs)

    def __rsub__(self, lhs):
        return self.cast(lhs) + -self

    def __mul__(self, rhs):
        result = Counter()
        for m, c in self.terms.items():
            for n, d in self.cast(rhs).terms.items():
                result[tuple(sorted(m + n))] += c * d
        return Poly(dict(result))

    __rmul__ = __mul__

    def degree(self):
        return max(map(len, self.terms), default=-1)

    def value(self, assignment):
        total = 0
        for monomial, coefficient in self.terms.items():
            term = coefficient
            for variable in monomial:
                term *= assignment[variable]
            total += term
        return total


def var(name):
    return Poly({(name,): 1})


@dataclass(frozen=True)
class Program:
    name: str
    initial: int
    halt: int
    # (source, destination, A displacement, B displacement, zero-tested counter)
    edges: tuple

    @property
    def halt_edge(self):
        indices = [i for i, edge in enumerate(self.edges)
                   if edge == (self.halt, self.halt, 0, 0, None)]
        assert len(indices) == 1
        return indices[0]


def certificate(program, horizon):
    assert horizon >= 1
    count = len(program.edges)
    selectors = [[var(f'w{t}_{e}') - 1 for e in range(count)]
                 for t in range(horizon)]
    counters = [[var(f'{letter}{t}') for t in range(horizon + 1)]
                for letter in 'ab']
    residuals = []

    def add(label, polynomial):
        residuals.append((label, Poly.cast(polynomial)))

    # Counter equations and boundary codes are reconstructed separately from
    # selector constraints. All finite edge data are coefficients.
    for t, row in enumerate(selectors):
        for c, letter in enumerate('ab'):
            displacement = sum(program.edges[e][2 + c] * row[e]
                               for e in range(count))
            add(f'update_{letter}_{t}', counters[c][t + 1] - counters[c][t] - displacement)
        for e, edge in enumerate(program.edges):
            if edge[4] is not None:
                c = 'ab'.index(edge[4])
                add(f'zero_{t}_{e}', row[e] * (counters[c][t] - 1))
        add(f'onehot_{t}', sum(row) - 1)
        for e, selector in enumerate(row):
            add(f'binary_{t}_{e}', selector * (selector - 1))
    source_codes = [sum(edge[0] * row[e] for e, edge in enumerate(program.edges))
                    for row in selectors]
    target_codes = [sum(edge[1] * row[e] for e, edge in enumerate(program.edges))
                    for row in selectors]
    add('initial_code', source_codes[0] - program.initial)
    for t in range(horizon - 1):
        add(f'linked_code_{t}', target_codes[t] - source_codes[t + 1])
    add('final_code', target_codes[-1] - program.halt)
    early = sum(row[program.halt_edge] for row in selectors)
    polynomial = sum(r * r for _, r in residuals)
    exact = polynomial + early * early
    names = {'a0', 'b0'} | {f'{c}{t}' for c in 'ab' for t in range(1, horizon + 1)}
    names |= {f'w{t}_{e}' for t in range(horizon) for e in range(count)}
    return residuals, early, polynomial, exact, names


H = 101
PROGRAMS = {
    'halt_only': Program('halt_only', H, H, ((H, H, 0, 0, None),)),
    'halt_zero_code': Program('halt_zero_code', 0, 0, ((0, 0, 0, 0, None),)),
    'inc_a': Program('inc_a', -17, H, ((-17, H, 1, 0, None), (H, H, 0, 0, None))),
    'inc_b': Program('inc_b', -17, H, ((-17, H, 0, 1, None), (H, H, 0, 0, None))),
    'a_equal_targets': Program('a_equal_targets', -17, H,
        ((-17, H, 0, 0, 'a'), (-17, H, -1, 0, None), (H, H, 0, 0, None))),
    'b_equal_targets': Program('b_equal_targets', -17, H,
        ((-17, H, 0, 0, 'b'), (-17, H, 0, -1, None), (H, H, 0, 0, None))),
    'count_a_into_b': Program('count_a_into_b', 0, 2,
        ((0, 2, 0, 0, 'a'), (0, 1, -1, 0, None), (1, 0, 0, 1, None), (2, 2, 0, 0, None))),
    'inc_loop': Program('inc_loop', -17, H,
        ((-17, -17, 1, 0, None), (H, H, 0, 0, None))),
    'mixed_seven_edges': Program('mixed_seven_edges', -17, H,
        ((-17, 23, 1, 0, None), (23, 41, 0, 1, None),
         (41, H, 0, 0, 'a'), (41, 67, -1, 0, None),
         (67, H, 0, 0, 'b'), (67, -17, 0, -1, None), (H, H, 0, 0, None)))
}


def declared_fixture(program, inputs, selected_edges, next_counters):
    assert len(selected_edges) == len(next_counters)
    assignment = {'a0': inputs[0], 'b0': inputs[1]}
    for t, (edge, pair) in enumerate(zip(selected_edges, next_counters)):
        assignment.update({f'w{t}_{e}': 1 + (e == edge) for e in range(len(program.edges))})
        assignment.update({f'a{t+1}': pair[0], f'b{t+1}': pair[1]})
    return assignment


def inspect_fixture(name, program, assignment, expected, exact_expected=None, positive=True):
    horizon = len([k for k in assignment if k.startswith('a')]) - 1
    residuals, early, polynomial, exact, names = certificate(program, horizon)
    assert set(assignment) == names
    values = {label: residual.value(assignment) for label, residual in residuals}
    pvalue = polynomial.value(assignment)
    evalue = exact.value(assignment)
    assert pvalue == sum(v * v for v in values.values()) == expected
    assert evalue == pvalue + early.value(assignment) ** 2
    assert all(v > 0 for v in assignment.values()) == positive
    if exact_expected is not None:
        assert evalue == exact_expected
    return {'name': name, 'polynomial': pvalue, 'exact_polynomial': evalue,
            'positive_domain': positive, 'nonzero_residuals': {k: v for k, v in values.items() if v}}


def enumerate_polynomial_solutions(program, horizon, inputs):
    """Exhaustive algebraic elimination, not a step-by-step execution.

    Binary and one-hot equations leave precisely E**T whole words. For every
    candidate word, each counter variable is obtained directly by a prefix sum
    of fixed coefficients, the unique solution of the linear update equations.
    All remaining polynomial equations and domain inequalities are then tested.
    No enabled-next-edge operation is implemented.
    """
    residuals, early, _, _, _ = certificate(program, horizon)
    remaining = [(label, r) for label, r in residuals
                 if not label.startswith(('binary_', 'onehot_', 'update_'))]
    answers = []
    exact_count = 0
    candidates = 0
    for word in product(range(len(program.edges)), repeat=horizon):
        candidates += 1
        # Direct simultaneous affine elimination; every full word is considered.
        pairs = [(inputs[0] + sum(program.edges[word[j]][2] for j in range(k)),
                  inputs[1] + sum(program.edges[word[j]][3] for j in range(k)))
                 for k in range(1, horizon + 1)]
        assignment = declared_fixture(program, inputs, word, pairs)
        if min(assignment.values()) <= 0:
            continue
        if all(r.value(assignment) == 0 for _, r in remaining):
            answers.append(list(word))
            exact_count += (early.value(assignment) == 0)
    return {'horizon': horizon, 'inputs': list(inputs), 'candidate_words': candidates,
            'positive_solution_count': len(answers), 'exact_solution_count': exact_count,
            'solution_words': answers}


def read_source(source, relative):
    with os.fdopen(os.open(source / relative, os.O_RDONLY | os.O_NOATIME), 'rb') as stream:
        return stream.read()


def replay_paths():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', required=True, type=Path,
                        help='absolute directory containing the pinned arithmetic packet')
    parser.add_argument('--output-dir', required=True, type=Path,
                        help='fresh nonexistent absolute output directory outside source and checker')
    parser.add_argument('--protected-root', action='append', type=Path, default=[],
                        help='additional absolute read-only tree, e.g. an extracted release root')
    args = parser.parse_args()
    if not args.source.is_absolute() or not args.output_dir.is_absolute():
        parser.error('source and output paths must be absolute')
    source = args.source.resolve(strict=True)
    if not source.is_dir():
        parser.error('source must be a directory')
    # Reject aliases before canonicalizing, including a dangling final symlink.
    if any(p.is_symlink() for p in (args.output_dir, *args.output_dir.parents)):
        parser.error('output path and its parents must not contain symlinks')
    output = args.output_dir.resolve(strict=False)
    if any(not p.is_absolute() for p in args.protected_root):
        parser.error('protected roots must be absolute')
    protected_roots = [p.resolve(strict=True) for p in args.protected_root]
    for protected in (source, HERE, *protected_roots):
        if output == protected or output in protected.parents or protected in output.parents:
            parser.error('output must not overlap the source or checker tree')
    if output.exists():
        parser.error('output directory must be fresh and nonexistent')
    return source, output


def main():
    source, output = replay_paths()
    manifest_bytes = read_source(source, 'MANIFEST.json')
    assert hashlib.sha256(manifest_bytes).hexdigest() == EXPECTED_MANIFEST
    manifest = json.loads(manifest_bytes)
    assert manifest['files']['PROOF.md'] == EXPECTED_PROOF
    for name, digest in manifest['files'].items():
        assert hashlib.sha256(read_source(source, name)).hexdigest() == digest
    results = {'source_proof_sha256': EXPECTED_PROOF,
               'source_manifest_sha256': EXPECTED_MANIFEST,
               'all_manifest_entries_verified': True, 'schema_checks': [],
               'fixtures': [], 'exhaustive_polynomial_checks': []}
    for name, program in PROGRAMS.items():
        E = len(program.edges)
        Z = sum(edge[4] is not None for edge in program.edges)
        for T in range(1, 7):
            residuals, early, p, exact, names = certificate(program, T)
            assert len(names) - 2 == T * (E + 2)
            assert len(residuals) == T * (E + Z + 4) + 1
            assert all(r.degree() <= 2 for _, r in residuals)
            assert p.degree() == exact.degree() == 4
            assert early.degree() == 1
            assert {v for monomial in p.terms for v in monomial} == names
            for t in range(T):
                for e in range(E):
                    key = (f'w{t}_{e}',) * 4
                    assert p.terms[key] == exact.terms[key] == 1
            assert all(type(c) is int for c in p.terms.values())
            results['schema_checks'].append({'program': name, 'T': T, 'E': E, 'Z': Z,
                'witnesses': len(names)-2, 'residuals': len(residuals),
                'exact_residuals': len(residuals)+1, 'degree': p.degree(), 'monomials': len(p.terms)})

    def fixture(name, key, inputs, word, pairs, expected=0, exact=None, positive=True):
        p = PROGRAMS[key]
        a = declared_fixture(p, inputs, word, pairs)
        results['fixtures'].append(inspect_fixture(name, p, a, expected, exact, positive))
        return a

    fixture('immediate_A_zero', 'a_equal_targets', (1, 3), [0], [(1, 3)], exact=0)
    fixture('immediate_A_positive', 'a_equal_targets', (2, 3), [1], [(1, 3)], exact=0)
    fixture('immediate_B_zero', 'b_equal_targets', (3, 1), [0], [(3, 1)], exact=0)
    fixture('immediate_B_positive', 'b_equal_targets', (3, 2), [1], [(3, 1)], exact=0)
    fixture('A_zero_on_positive_rejected', 'a_equal_targets', (2, 3), [0], [(2, 3)], expected=1)
    fixture('B_zero_on_positive_rejected', 'b_equal_targets', (3, 2), [0], [(3, 2)], expected=1)
    fixture('A_decrement_zero_domain_rejected', 'a_equal_targets', (1, 3), [1], [(0, 3)], positive=False)
    fixture('B_decrement_zero_domain_rejected', 'b_equal_targets', (3, 1), [1], [(3, 0)], positive=False)
    fixture('A_illegal_decrement_positive_fake_output', 'a_equal_targets', (1, 3), [1], [(1, 3)], expected=1)
    fixture('B_illegal_decrement_positive_fake_output', 'b_equal_targets', (3, 1), [1], [(3, 1)], expected=1)
    fixture('increment_A', 'inc_a', (1, 2), [0], [(2, 2)], exact=0)
    fixture('increment_B', 'inc_b', (2, 1), [0], [(2, 2)], exact=0)
    fixture('initially_halted_positive_horizon', 'halt_only', (4, 3), [0, 0, 0], [(4, 3)] * 3, exact=9)
    a = fixture('declared_three_step', 'count_a_into_b', (2, 1), [1, 2, 0], [(1, 1), (1, 2), (1, 2)], exact=0)
    fixture('declared_padded_four_step', 'count_a_into_b', (2, 1), [1, 2, 0, 3],
            [(1, 1), (1, 2), (1, 2), (1, 2)], exact=1)
    p = PROGRAMS['count_a_into_b']
    for name, updates in [
        ('selector_zero', {'w0_1': 0}), ('selector_three', {'w0_1': 3}),
        ('no_selected_edge', {'w0_1': 1}), ('two_selected_edges', {'w0_0': 2}),
        ('wrong_next_counter', {'a1': 2}), ('wrong_control', {'w1_2': 1, 'w1_3': 2}),
        ('wrong_final_control', {'w2_0': 1, 'w2_1': 2})]:
        changed = a | updates
        residuals, early, polynomial, exact, names = certificate(p, 3)
        value = polynomial.value(changed)
        assert value > 0
        results['fixtures'].append(inspect_fixture(name, p, changed, value,
                                                   positive=min(changed.values()) > 0))

    # Independent complete enumeration for finite test instances. The expected
    # hitting-time formula of the declared count graph is 2*(A-1)+1.
    for key in ['count_a_into_b', 'a_equal_targets', 'b_equal_targets', 'halt_only', 'inc_loop']:
        p = PROGRAMS[key]
        for T in range(1, 6):
            for A, B in product(range(1, 5), range(1, 3)):
                row = enumerate_polynomial_solutions(p, T, (A, B))
                k = {'count_a_into_b': 2*(A-1)+1, 'a_equal_targets': 1,
                     'b_equal_targets': 1, 'halt_only': 0, 'inc_loop': None}[key]
                assert row['positive_solution_count'] == int(k is not None and k <= T)
                assert row['exact_solution_count'] == int(k is not None and k == T)
                results['exhaustive_polynomial_checks'].append({'program': key} | row)
    row = enumerate_polynomial_solutions(PROGRAMS['count_a_into_b'], 7, (4, 2))
    assert row['positive_solution_count'] == row['exact_solution_count'] == 1
    results['exhaustive_polynomial_checks'].append({'program': 'count_a_into_b'} | row)

    # The no-duplicate-enabled-edges hypothesis is necessary: intentionally
    # violate it and obtain two distinct selector tuples for the same counters.
    duplicate = Program('excluded_duplicate_increment', -17, H,
        ((-17, H, 1, 0, None), (-17, H, 1, 0, None), (H, H, 0, 0, None)))
    row = enumerate_polynomial_solutions(duplicate, 1, (1, 1))
    assert row['positive_solution_count'] == 2
    results['excluded_duplicate_edges_counterexample'] = row
    results['horizon_zero'] = {'initially_halted_constant': (H-H)**2,
        'nonhalted_constant': (-17-H)**2, 'witnesses': 0, 'applies_quartic_ledger': False}
    assert results['horizon_zero']['initially_halted_constant'] == 0
    assert results['horizon_zero']['nonhalted_constant'] == 13924

    # Check the frozen author's saved numbers as data only, never execute its file.
    author_evidence = json.loads(read_source(source, 'evidence/static_checks.json'))
    own_ledgers = [x for x in results['schema_checks'] if x['program'] == 'count_a_into_b' and x['T'] <= 4]
    for own, old in zip(own_ledgers, author_evidence['ledgers']):
        assert own['T'] == old['horizon']
        assert own['monomials'] == old['expanded_monomials']
        assert own['witnesses'] == old['positive_witnesses']
        assert own['residuals'] == old['residuals']
    results['frozen_saved_ledger_numbers_reproduced_independently'] = True
    results['schema_instance_count'] = len(results['schema_checks'])
    results['exhaustive_instance_count'] = len(results['exhaustive_polynomial_checks'])
    results['exhaustive_candidate_words'] = sum(row['candidate_words'] for row in results['exhaustive_polynomial_checks'])
    results['checker_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    output.mkdir(parents=True, exist_ok=False)
    (output/'independent_results.json').write_text(json.dumps(results, indent=2)+'\n')
    print(json.dumps({k: results[k] for k in ('source_proof_sha256', 'source_manifest_sha256',
          'schema_instance_count', 'exhaustive_instance_count', 'exhaustive_candidate_words', 'checker_sha256')}, indent=2))
    print('PASS: independent schema, quartic coefficients, guards, adversarial fixtures, and exhaustive finite polynomial uniqueness')


if __name__ == '__main__':
    main()
