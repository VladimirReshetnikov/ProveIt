#!/usr/bin/env python3
"""Independently audit the three-mass generator's exact finite-size ledger.

Standard-library only. Run:
    python verify_size_ledger.py --generator /path/to/three_mass_collision_generator.py
No source-generator files are modified. The JSON receipt can be redirected to a file.
"""
import argparse
from collections import Counter
import hashlib
import importlib.util
import json
from pathlib import Path
import sys


def load_generator(path):
    spec = importlib.util.spec_from_file_location('three_mass_ledger_subject', path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def formula(q, m, d):
    return {
        'types': 96*q*m + 6*q*d + 2*d + 6*q + 2314,
        'prescribed_pairs': 3528*q*m + 6*q*d + d - 6*m + 1152,
        'overlap_vertices': 48*q*m - 6*m - 6*q,
        'completed_pairs': 7008*q*m + 12*q*d + 2*d + 6*q - 6*m + 2304,
    }


def audit_case(module, label, states, halt, instructions):
    class ObservedCA(module.ThreeMassCA):
        def _complete_pairs(self):
            self.before = dict(self.pairs)
            self.types_before_completion = len(self.names)
            super()._complete_pairs()

    assert len(set(states)) == len(states) and halt in states
    assert all(i.source in states and i.target in states for i in instructions)
    ca = ObservedCA(states, halt, instructions)
    q, m = len(states), len(instructions) + 1
    d = sum(i.operation in ('inc', 'dec') for i in instructions)
    D = 6*q*m
    expected = formula(q, m, d)
    family = Counter(name[0] for name in ca.names)
    assert family == Counter({
        'L': 8*D, 'S': 8, 'wait': 8*D, 'clock': 2304,
        'moving': 6*q*d, 'arith': 2*d, 'trap': 6*q, 'escape': 1, 'R': 1,
    }), (label, family)
    domain, image = set(ca.before), set(ca.before.values())
    overlap = domain & image
    assert len(image) == len(domain) == ca.required_pair_count
    observed = {
        'types': len(ca.names),
        'prescribed_pairs': len(ca.before),
        'overlap_vertices': len(overlap),
        'completed_pairs': len(ca.pairs),
    }
    assert observed == expected, (label, expected, observed)
    static = {}
    for pair in overlap:
        names = [ca.names[t] for t in pair]
        L = next((name for name in names if name[0] == 'L'), None)
        S = next((name for name in names if name[0] == 'S'), None)
        assert L is not None and S is not None and L[1] == S[1], (label, names)
        static[pair] = L[1]
    assert Counter(static.values()) == Counter({
        stage: D - (6*m if stage == 0 else 6*q if stage == 5 else 0)
        for stage in range(8)
    })
    starts = domain - image
    visited_edges = set()
    path_lengths = Counter()
    for start in starts:
        cursor = start
        length = 0
        while cursor in ca.before:
            assert cursor not in visited_edges, (label, 'path collision or cycle')
            visited_edges.add(cursor)
            cursor = ca.before[cursor]
            length += 1
        assert ca.pairs[cursor] == start
        path_lengths[length] += 1
    assert visited_edges == domain, (label, 'prescribed graph has a cycle')
    assert len(starts) == expected['prescribed_pairs'] - expected['overlap_vertices']
    assert len(ca.pairs) - len(ca.before) == len(starts)
    assert set(ca.pairs) == set(ca.pairs.values())
    # The public constructor and valid initial/ready lookups must not lazily add types.
    assert ca.types_before_completion == len(ca.names)
    for state in states:
        for stage in range(8):
            for i, z in ((0, 0), (m-1, 5)):
                ca.ready(ca.initial(state, 1, i=i, z=z, stage=stage))
    assert len(ca.names) == expected['types']
    return {
        'case': label, 'q': q, 'm': m, 'd': d, **observed,
        'completion_rows_added': len(starts),
        'prescribed_path_lengths': dict(sorted(path_lengths.items())),
        'radius_one_types': 4*expected['types'],
        'radius_one_alphabet': '2^' + str(4*expected['types']),
    }


def cases(module):
    I = module.Instruction
    yield 'minimal_halt_only', ['h'], 'h', []
    yield 'unused_states_no_instructions', ['a', 'b', 'c', 'h'], 'h', []
    for operation in ('inc', 'dec', 'nop', 'zero', 'positive'):
        for counter in (0, 1):
            yield f'single_{operation}_counter_{counter}', ['a', 'h'], 'h', [I('a', 'h', operation, counter)]
            yield f'self_loop_{operation}_counter_{counter}', ['a', 'h'], 'h', [I('a', 'a', operation, counter)]
    # Source guards can branch and inverse guards can merge without affecting sizes.
    for counter in (0, 1):
        yield f'guarded_split_{counter}', ['a', 'b', 'h'], 'h', [
            I('a', 'b', 'zero', counter), I('a', 'h', 'positive', counter)]
        yield f'guarded_merge_{counter}', ['a', 'b', 'h'], 'h', [
            I('a', 'h', 'zero', counter), I('b', 'h', 'positive', counter)]
        yield f'guarded_double_self_loop_{counter}', ['a', 'h'], 'h', [
            I('a', 'a', 'zero', counter), I('a', 'a', 'positive', counter)]
    yield 'four_arithmetic_cycle', ['q0', 'q1', 'q2', 'q3', 'h'], 'h', [
        I('q0', 'q1', 'inc', 0), I('q1', 'q2', 'inc', 1),
        I('q2', 'q3', 'dec', 0), I('q3', 'q0', 'dec', 1)]
    yield 'mixed_cycle_unused_state', ['a', 'b', 'c', 'unused', 'h'], 'h', [
        I('a', 'b', 'inc', 1), I('b', 'c', 'nop', 0), I('c', 'a', 'dec', 1)]
    # The count also survives accepted raw-generator inputs with outgoing halt rules.
    # These are size stress tests, not properly terminal source machines.
    for operation in ('inc', 'nop', 'zero'):
        yield f'raw_halt_self_loop_{operation}', ['h'], 'h', [I('h', 'h', operation, 0)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--generator', type=Path,
                        default=Path(__file__).resolve().parent / 'three_mass_collision_generator.py')
    args = parser.parse_args()
    module = load_generator(args.generator)
    results = [audit_case(module, *case) for case in cases(module)]
    print(json.dumps({
        'status': 'passed',
        'generator_sha256': hashlib.sha256(args.generator.read_bytes()).hexdigest(),
        'case_count': len(results),
        'checks': ['exact type-family counts', 'exact prescribed/completed pair counts',
                   'exact overlap by stage', 'all prescribed components are paths',
                   'every completion closes its own path', 'completion creates no types',
                   'valid initial/ready calls create no types'],
        'cases': results,
    }, indent=2))


if __name__ == '__main__':
    main()
