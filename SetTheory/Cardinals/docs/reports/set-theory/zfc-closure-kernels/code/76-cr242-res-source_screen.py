#!/usr/bin/env python3
"""Finite source-layout screens after the QT rotation.

This does not emit a Turing machine or infer a working-state count from a
source-DAG count. All mutations and outputs are external to the repository.

The numerical program/calculus is due to Mira-Cult, with verification by
Jeff Ketchersid and the compiler framework by Andrew James Wade. The path
semantics and the two QT loop associations follow the source71 contribution
retained in ProveIt. This script adds their simultaneous four-H-loop census
on the combined243 source and checks its own full source contexts.
"""
from pathlib import Path
from itertools import product
from collections import Counter
from hashlib import sha256
import argparse
import json


def inc(path):
    if not path:
        return ''
    return format((int(path, 2) + 1) % (1 << len(path)), f'0{len(path)}b')


def jump(path, bit, count):
    indices = [i for i in range(len(path)-1, -1, -1) if path[i] == bit]
    stem = path[:indices[count-1]] if count <= len(indices) else ''
    return inc(stem) if bit == '0' else stem


class Program:
    def __init__(self, sites):
        self.sites = sites
        self.leaves = {p: i for i, (p, _, _) in enumerate(sites)}
        assert len(self.leaves) == len(sites)
        assert sorted(self.leaves) == [p for p, _, _ in sites]
        self.depth = max(map(len, self.leaves))
        self.prefixes = {p[:i] for p in self.leaves for i in range(len(p))}
        assert not self.prefixes.intersection(self.leaves)
        domain = self.prefixes | self.leaves.keys()
        assert all(p+'0' in domain and p+'1' in domain for p in self.prefixes)

    def lookup(self, path):
        for n in range(1, self.depth + 1):
            p = (path + '0'*self.depth)[:n]
            if p in self.leaves:
                assert set(path[n:]) <= {'0'}
                return self.leaves[p]
        raise AssertionError(path)

    def successors(self, i):
        p, op, n = self.sites[i]
        if op == 'CH':
            return {}
        if op == 'CI':
            result = {'inc': inc(p)}
        elif op == 'CD':
            result = {'zero': jump(p, '0', 1), 'positive': inc(p)}
        else:
            result = {'control': jump(p, '0' if op == 'CB' else '1', n)}
        return {k: self.lookup(v) for k, v in result.items()}


def tree_of(sites):
    leaves = {p: ('L', op, n) for p, op, n in sites}
    subtrees = {}
    def walk(p=''):
        if p in leaves:
            return leaves[p]
        result = ('N', walk(p+'0'), walk(p+'1'))
        subtrees[p] = result
        return result
    root = walk()
    return root, subtrees


def sites_of(root):
    out = []
    def walk(t, p=''):
        if t[0] == 'L':
            out.append([p, t[1], t[2]])
        else:
            walk(t[1], p+'0')
            walk(t[2], p+'1')
    walk(root)
    return out


def count_nodes(root):
    seen = set()
    def walk(t):
        if t[0] == 'N' and t not in seen:
            seen.add(t)
            walk(t[1])
            walk(t[2])
    walk(root)
    return len(seen)


def rotation(register, left):
    a, b = ('L', 'CI', register), ('L', 'CD', 6)
    return (('N', ('N', a, b), ('L', 'CC', 1)) if left
            else ('N', a, ('N', b, ('L', 'CC', 2))))


def replace(root, edits):
    def walk(t, p=''):
        if p in edits:
            return edits[p]
        if t[0] == 'L':
            return t
        return ('N', walk(t[1], p+'0'), walk(t[2], p+'1'))
    return walk(root)


def context_check(old, new, prefixes):
    """Every outside edge commutes; no outside edge enters a changed interior."""
    old_members = {i: p for p in prefixes for i, row in enumerate(old.sites)
                   if row[0].startswith(p)}
    new_members = {i: p for p in prefixes for i, row in enumerate(new.sites)
                   if row[0].startswith(p)}
    old_entries = {p: min(i for i, q in old_members.items() if q == p) for p in prefixes}
    new_entries = {p: min(i for i, q in new_members.items() if q == p) for p in prefixes}
    mapping = {i: new.leaves[row[0]] for i, row in enumerate(old.sites) if i not in old_members}
    mapping.update({old_entries[p]: new_entries[p] for p in prefixes})
    edges = 0
    for i, j in mapping.items():
        if i in old_members:
            continue
        assert old.sites[i][1:] == new.sites[j][1:]
        a, b = old.successors(i), new.successors(j)
        assert a.keys() == b.keys()
        for guard, target in a.items():
            assert target in mapping, ('outside entry to changed interior', i, guard, target)
            assert mapping[target] == b[guard]
            edges += 1
    assert mapping[old.lookup('')] == new.lookup('')
    return edges


def loop_contract(program, prefix, register, rotated):
    """Universal equal-register blocks, split into X=0 and X>=1.

    Other registers remain formal independent naturals. Only constant deltas
    and forced lower/upper bounds are propagated; this is not numerical testing.
    """
    members = [i for i, row in enumerate(program.sites) if row[0].startswith(prefix)]
    entry, after = min(members), max(members) + 1
    records = []
    for zero, duration in [(True, 2), (False, 3)]:
        lower = [0]*9
        upper = [None]*9
        if zero:
            upper[6] = 0
        else:
            lower[6] = 1
        delta = [0]*9
        i = entry
        trace = []
        for _ in range(duration):
            _, op, arg = program.sites[i]
            successors = program.successors(i)
            if op == 'CI':
                assert arg == register
                delta[arg] += 1
                lower[arg] += 1
                if upper[arg] is not None:
                    upper[arg] += 1
                guard = 'inc'
            elif op == 'CD':
                assert arg == 6
                if upper[arg] == 0:
                    guard = 'zero'
                else:
                    assert lower[arg] >= 1
                    lower[arg] -= 1
                    delta[arg] -= 1
                    if upper[arg] is not None:
                        upper[arg] -= 1
                    guard = 'positive'
            else:
                assert op == 'CC'
                guard = 'control'
            trace.append([i, guard])
            i = successors[guard]
        expected = [0]*9
        expected[register] = 1
        if not zero:
            expected[6] = -1
        assert delta == expected
        assert i == (after if zero else entry)
        records.append({'guard': 'X=0' if zero else 'X>=1',
                        'clock': duration, 'register_delta': delta,
                        'end': 'after' if zero else 'entry'})
    return records


def main():
    if not __debug__:
        raise RuntimeError('Assertions must be enabled.')
    ap = argparse.ArgumentParser()
    ap.add_argument('--sites', type=Path, required=True)
    ap.add_argument('--mod4', type=Path)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    sites = json.loads(args.sites.read_text())
    old = Program(sites)
    root, subtrees = tree_of(sites)
    assert len(sites) == 6459 and count_nodes(root) == 202
    needle = ('N', ('N', ('L', 'CD', 6),
                     ('N', ('L', 'CI', 5), ('L', 'CC', 2))), ('L', 'CI', 5))
    candidates = sorted(p for p, t in subtrees.items() if t == needle)
    assert candidates == ['11101001001011000011', '1110100100101110011',
                          '1110100101100011', '111110011']
    # Existing QT is already a rotated loop; the four H loops have the old form.
    baseline_contracts = {p: loop_contract(old, p, 5, False) for p in candidates}
    baseline_contracts['011'] = loop_contract(old, '011', 0, True)
    results = []
    for mask in product(range(3), repeat=4):
        for qt_left in range(2):
            edits = {'011': rotation(0, qt_left)}
            edits.update({p: rotation(5, v-1) for p, v in zip(candidates, mask) if v})
            t = replace(root, edits)
            new = Program(sites_of(t))
            outside = context_check(old, new, edits)
            for p in edits:
                assert loop_contract(new, p, 0 if p == '011' else 5, True) == baseline_contracts[p]
            results.append({'H_loop_choices': list(mask), 'QT_left': bool(qt_left),
                            'source_leaves': len(new.sites),
                            'unique_decoder_nodes': count_nodes(t),
                            'checked_outside_edges': outside})
    report = {
        'status': 'PASS_FINITE_SOURCE_SCREEN_NO_REDUCED_MACHINE',
        'baseline_repository_commit': 'e58338db7545909907e07a7603e8eb88625c527a',
        'baseline_repository_path': 'Computability/BusyBeaver/Research/ZFC/candidate-combined243/sites_logical.json',
        'input_source_sha256': sha256(args.sites.read_bytes()).hexdigest(),
        'baseline_source_leaves': len(sites), 'baseline_unique_decoder_nodes': 202,
        'loop_source_contract': 'For every natural entry register tuple, return with R6=0, Rdest=Rdest+old_R6+1, preserving the other seven registers.',
        'loop_induction': 'Each positive three-instruction block lowers R6 by one; the zero two-instruction block exits. The exact source duration is 3*old_R6+2.',
        'H_loop_prefixes': candidates, 'choice_meaning': {'0': 'original', '1': 'right rotation', '2': 'left rotation'},
        'layout_count': len(results),
        'node_histogram': dict(sorted(Counter(x['unique_decoder_nodes'] for x in results).items())),
        'minimum_unique_decoder_nodes': min(x['unique_decoder_nodes'] for x in results),
        'source_context_and_unbounded_loop_blocks_checked': True,
        'layouts': results,
        'scope': 'Exact finite layout census and ordinary universal source equivalence. Decoder-node counts are not Turing-machine working-state counts. No optimality beyond this finite family and no candidate table is claimed.'}
    if args.mod4:
        alternatives = json.loads(args.mod4.read_text())['7']['candidates']
        assert len(alternatives) == 19
        prefix = '1110100101'
        common = [r for r in sites if not r[0].startswith(prefix)]
        common += [[prefix+'1'+p[len(prefix)+2:], op, a]
                   for p, op, a in sites if p.startswith(prefix+'11')]
        counts = []
        for i, c in enumerate(alternatives):
            replacement = []
            for p, op in zip(c['paths'], c['ops']):
                kind, arg = (('CD', 5) if op == 'D' else ('CH', None) if op == 'H'
                             else ('CC' if op[0] == 'C' else 'CB', int(op[1:])))
                replacement.append([prefix+'0'+p, kind, arg])
            ns = sorted(common + replacement)
            Program(ns)
            nt, _ = tree_of(ns)
            counts.append({'candidate': i, 'source_leaves': len(ns),
                           'unique_decoder_nodes': count_nodes(nt)})
        report['modulo4_layout_counts'] = counts
        report['modulo4_scope'] = 'Only exact prefix-tree validity and decoder-DAG cost are checked here. The modulus tester theorem, logical admission theorem, runtime and initialization are separate obligations; no Turing-machine candidate is built.'
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k: report[k] for k in ['status', 'layout_count', 'node_histogram', 'minimum_unique_decoder_nodes']}, indent=2))


if __name__ == '__main__':
    main()
