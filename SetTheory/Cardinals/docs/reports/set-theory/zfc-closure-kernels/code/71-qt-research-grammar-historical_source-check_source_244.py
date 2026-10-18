#!/usr/bin/env python3
"""Independent inductive-invariant and source weak-bisimulation check.

No imports from the table builder, invariant producer, or earlier proof package.
The only mathematical domain convention is that upper endpoint 9 means infinity.
Run without -O: every claim is checked by an assertion.
"""
from pathlib import Path
from hashlib import sha256
import argparse
import json
from collections import Counter

CAP = 8
INFINITY = 9
P = '1110100101100011'
REMOVED_TEST = 6316
REMOVED_BODY = (6317, 6318)
RETAINED_INC = 6319
DIRTY_ZERO_REGISTERS = {1, 2, 5}


def increment_path(path):
    if not path:
        return ''
    # Binary successor modulo 2^length, deliberately retaining leading zeros.
    return format((int(path, 2) + 1) % (1 << len(path)), f'0{len(path)}b')

def remove_through(path, bit, count):
    assert type(count) is int and count > 0
    positions = [j for j in range(len(path) - 1, -1, -1) if path[j] == bit]
    return path[:positions[count-1]] if count <= len(positions) else ''

def jump(path, bit, count):
    stem = remove_through(path, bit, count)
    return increment_path(stem) if bit == '0' else stem


class Program:
    def __init__(self, sites):
        self.sites = sites
        self.leaves = {}
        self.prefixes = set()
        for i, row in enumerate(sites):
            assert isinstance(row, list) and len(row) == 3
            path, opcode, arg = row
            assert path and set(path) <= {'0', '1'}
            assert opcode in {'CI', 'CD', 'CB', 'CC', 'CH'}
            assert ((opcode in {'CI', 'CD'} and type(arg) is int and 0 <= arg < 9)
                    or (opcode in {'CB', 'CC'} and type(arg) is int and arg > 0)
                    or (opcode == 'CH' and arg is None))
            assert path not in self.leaves
            self.leaves[path] = i
            self.prefixes.update(path[:j] for j in range(len(path)))
        assert not self.prefixes.intersection(self.leaves)
        nodes = self.prefixes | self.leaves.keys()
        for stem in self.prefixes:
            assert stem + '0' in nodes and stem + '1' in nodes
        assert [path for path, _, _ in sites] == sorted(self.leaves)
        self.depth = max(map(len, self.leaves))

    def site_at(self, path):
        assert set(path) <= {'0', '1'}
        for length in range(1, self.depth + 1):
            prefix = (path + '0' * length)[:length]
            if prefix in self.leaves:
                assert set(path[length:]) <= {'0'}, ('discarded nonzero path suffix', path, prefix)
                return self.leaves[prefix]
        raise AssertionError(('path does not reach a leaf', path))

    def successors(self, index):
        """Return branch label -> destination; arithmetic effect is separate."""
        path, op, arg = self.sites[index]
        if op == 'CH':
            return {}
        if op == 'CI':
            targets = {'inc': increment_path(path)}
        elif op == 'CD':
            targets = {'zero': jump(path, '0', 1), 'positive': increment_path(path)}
        elif op == 'CB':
            targets = {'control': jump(path, '0', arg)}
        else:
            targets = {'control': jump(path, '1', arg)}
        return {case: self.site_at(dest) for case, dest in targets.items()}


def box(value):
    if value is None:
        return None
    assert isinstance(value, list) and len(value) == 9
    for lo, hi in value:
        assert type(lo) is int and type(hi) is int
        assert 0 <= lo <= CAP and lo <= hi <= INFINITY
    return tuple(tuple(pair) for pair in value)


def contained(inner, outer):
    """The infinity code is above every finite upper endpoint."""
    assert outer is not None
    return all(a <= x and y <= b for (x, y), (a, b) in zip(inner, outer))


def image_bounds(row, value, case):
    _, op, register = row
    if op in {'CB', 'CC'}:
        assert case == 'control'
        return value
    lo, hi = value[register]
    if op == 'CI':
        assert case == 'inc'
        pair = (min(CAP, lo + 1), min(INFINITY, hi + 1))
    elif case == 'zero':
        if lo != 0:
            return None
        pair = (0, 0)
    else:
        assert op == 'CD' and case == 'positive'
        if hi == 0:
            return None
        pair = (max(1, lo) - 1, INFINITY if hi == INFINITY else hi - 1)
    return value[:register] + (pair,) + value[register + 1:]


def check_interval_certificate(program, certificate):
    values = [box(value) for value in certificate['invariants']]
    assert len(values) == len(program.sites) == 6460
    initial = tuple((0, 0) if r in DIRTY_ZERO_REGISTERS else (0, INFINITY) for r in range(9))
    assert box(certificate['initial']) == initial
    assert contained(initial, values[program.site_at('')])
    edges = 0
    branch_counts = Counter()
    for i, value in enumerate(values):
        if value is None:
            continue
        for branch, successor in program.successors(i).items():
            image = image_bounds(program.sites[i], value, branch)
            if image is None:
                continue
            assert contained(image, values[successor]), (i, branch, successor, image, values[successor])
            edges += 1
            branch_counts[branch] += 1
    assert edges == certificate['edges'] == 8384
    assert values[REMOVED_TEST][6] == (0, 0)
    assert values[REMOVED_BODY[0]] is None and values[REMOVED_BODY[1]] is None
    return values, {'closure_edges': edges, 'branch_counts': dict(branch_counts),
                    'unreachable_sites': [i for i, value in enumerate(values) if value is None]}


def check_weak_bisimulation(old, new, values, supplied_mapping):
    expected_old_subtree = [[P + '00', 'CD', 6], [P + '010', 'CI', 5],
                            [P + '011', 'CC', 2], [P + '1', 'CI', 5]]
    assert old.sites[REMOVED_TEST:RETAINED_INC+1] == expected_old_subtree
    assert [row for row in old.sites if row[0].startswith(P)] == expected_old_subtree
    assert new.sites == old.sites[:REMOVED_TEST] + [[P, 'CI', 5]] + old.sites[RETAINED_INC+1:]
    assert len(new.sites) == 6457
    mapping = {}
    for i in range(len(old.sites)):
        if i in REMOVED_BODY:
            continue
        mapping[i] = i if i < REMOVED_TEST else REMOVED_TEST if i == REMOVED_TEST else i - 3
    assert mapping == {int(i): j for i, j in supplied_mapping.items()}
    assert mapping[old.site_at('')] == new.site_at('')
    assert old.successors(REMOVED_TEST)['zero'] == RETAINED_INC
    assert mapping[REMOVED_TEST] == mapping[RETAINED_INC]
    assert values[REMOVED_TEST][6] == (0, 0)
    checked_edges = 0
    checked_sites = 0
    for i, j in mapping.items():
        if i == REMOVED_TEST:
            continue
        assert old.sites[i][1:] == new.sites[j][1:], (i, j, 'opcode mismatch')
        left, right = old.successors(i), new.successors(j)
        assert left.keys() == right.keys()
        for branch, successor in left.items():
            assert successor in mapping, (i, branch, successor, 'edge to omitted body')
            assert mapping[successor] == right[branch], (i, j, branch, successor, right[branch])
            checked_edges += 1
        checked_sites += 1
    assert checked_sites == len(new.sites)
    return mapping, {'ordinary_related_sites': checked_sites,
                     'ordinary_commuting_edges': checked_edges,
                     'stuttering_edge': [REMOVED_TEST, 'zero', RETAINED_INC],
                     'max_old_steps_per_new_step': 2,
                     'max_consecutive_old_stutters': 1,
                     'halt_sites_old': [i for i, (_, op, _) in enumerate(old.sites) if op == 'CH'],
                     'halt_sites_new': [i for i, (_, op, _) in enumerate(new.sites) if op == 'CH']}


def derive_pruned_invariant(new, old_values, mapping):
    values = [None] * len(new.sites)
    for i, j in mapping.items():
        left, right = old_values[i], values[j]
        if left is not None:
            values[j] = left if right is None else tuple((min(a, c), max(b, d))
                                                         for (a, b), (c, d) in zip(left, right))
    edges, admitted = 0, []
    excluded = []
    for i, (row, value) in enumerate(zip(new.sites, values)):
        path, op, register = row
        cases = ['zero', 'positive'] if op == 'CD' else ['halt'] if op == 'CH' else ['inc'] if op == 'CI' else ['control']
        for case in cases:
            image = None if value is None else value if case == 'halt' else image_bounds(row, value, case)
            record = {'index': i, 'pc': path, 'opcode': op, 'argument': register, 'guard': case}
            if image is None:
                excluded.append(record)
                continue
            record['intervals'] = value
            admitted.append(record)
            if case != 'halt':
                successor = new.successors(i)[case]
                assert contained(image, values[successor]), (i, case, successor)
                edges += 1
    assert edges == 8383 and len(admitted) == 8384 and len(excluded) == 3
    return {'status': 'PASS_SOURCE_ONLY',
            'warning': 'This certifies the single-occurrence pruned source, not the 244-state TM table. The current TM patch also changes three live occurrences and fails its runtime contract.',
            'domain': {'lower_cap': CAP, 'infinity_upper_endpoint': INFINITY},
            'initial_condition': 'R1=R2=R5=0; other six registers arbitrary naturals',
            'site_count': len(new.sites), 'closure_edges': edges,
            'admitted_guarded_cases': len(admitted), 'excluded_guarded_cases': len(excluded),
            'invariants': values, 'admitted': admitted, 'excluded': excluded}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--reference', type=Path, default=Path(__file__).resolve().parent/'reference')
    ap.add_argument('--candidate', type=Path, default=Path(__file__).resolve().parent/'single_occurrence')
    ap.add_argument('--invariant', type=Path, default=Path(__file__).resolve().parent/'dirty_invariant.json')
    ap.add_argument('--boot', type=Path, default=Path(__file__).resolve().parent/'rejected_boot.json')
    ap.add_argument('--output', type=Path, default=Path(__file__).with_name('source_244_verification.json'))
    args = ap.parse_args()
    sources = {'old_sites': args.reference/'certificate/sites_logical.json',
               'new_sites': args.candidate/'sites_logical.json',
               'invariant': args.invariant, 'pruning': args.candidate/'pruning.json',
               'boot': args.boot}
    data = {key: json.loads(path.read_text()) for key, path in sources.items()}
    old, new = Program(data['old_sites']), Program(data['new_sites'])
    values, interval_result = check_interval_certificate(old, data['invariant'])
    mapping, bisim_result = check_weak_bisimulation(old, new, values,
                                                  data['pruning']['old_to_new_site_index'])
    pruned = derive_pruned_invariant(new, values, mapping)
    args.output.with_name('single_occurrence_pruned_invariant.json').write_text(json.dumps(pruned, indent=2) + '\n')
    boot_registers = data['boot']['logical_registers']
    assert len(boot_registers) == 9 and all(type(n) is int and n >= 0 for n in boot_registers)
    assert all(boot_registers[i] == 0 for i in DIRTY_ZERO_REGISTERS)
    assert boot_registers == [3, 0, 0, 0, 3, 0, 35, 0, 0]
    result = {'status': 'PASS',
              'scope': 'Independent universal source invariant replay and divergence-sensitive source weak bisimulation; does not itself check TM runtime or bootstrap execution.',
              'domain': {'lower_cap': CAP, 'infinity_upper_endpoint': INFINITY},
              'initial_condition': 'R1=R2=R5=0; R0,R3,R4,R6,R7,R8 arbitrary natural numbers.',
              'hashes': {key: sha256(path.read_bytes()).hexdigest() for key, path in sources.items()},
              'interval': interval_result, 'source_equivalence': bisim_result,
              'boot_seed_in_initial_condition': boot_registers,
              'local_invariants': [{'old_site': i, 'instruction': old.sites[i], 'intervals': values[i]}
                                   for i in range(6312, 6325)]}
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: value for key, value in result.items() if key not in {'hashes', 'local_invariants'}}, indent=2))


if __name__ == '__main__':
    assert __debug__, 'Assertions must be enabled; do not run with -O.'
    main()
