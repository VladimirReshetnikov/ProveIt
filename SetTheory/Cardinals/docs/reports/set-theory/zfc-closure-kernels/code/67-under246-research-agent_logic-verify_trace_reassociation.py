#!/usr/bin/env python3
"""Independent closed-trace equivalence checker, with optional affine swaps.

No search, optimization, or upstream trace-normalization module is imported.
Dependencies are built for every pair, and every adjacent exchange used by
the independent normalizer is checked against its semantic rule.
"""
from __future__ import annotations
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import heapq
import json
from pathlib import Path

from verify_reassociation import Decoder, read_json, read_literal, encode, BASE, LITERAL


def identity():
    return tuple(tuple(int(i == j) for j in range(10)) for i in range(10))


def multiply(a, b):
    return tuple(tuple(sum(a[i][k] * b[k][j] for k in range(10))
                       for j in range(10)) for i in range(10))


@lru_cache(None)
def summary(term):
    if term[0] == 'L':
        op, *args = term[1]
        return frozenset(args) if op in ('I', 'D') else frozenset(), op == 'H'
    children = term[1] if term[0] == 'S' else term[1:]
    footprints, flags = zip(*(summary(x) for x in children))
    return frozenset().union(*footprints), any(flags)


def add_vectors(a, b):
    return tuple(x + y for x, y in zip(a, b))


@lru_cache(None)
def increment_body(term):
    """Certify a finite fixed increment effect and normal/continue exit.

    The evaluator follows structural control rules.  An encountered decrement,
    halt or restart is rejected; no sample register valuation is used.
    """
    zero = (0,) * 9
    if term[0] == 'L':
        op, *args = term[1]
        if op == 'I':
            assert 0 <= args[0] < 9
            return tuple(int(i == args[0]) for i in range(9)), 0
        if op == 'C' and args[0] > 0:
            return zero, args[0]
        return None
    if term[0] == 'S':
        total = zero
        for child in term[1]:
            result = increment_body(child)
            if result is None or result[1] != 0:
                return None
            total = add_vectors(total, result[0])
        return total, 0
    a, b = term[1:]
    first = increment_body(a)
    if first is None:
        return None
    effect, control = first
    if control > 0:
        # A continue from the car propagates without running the cdr.
        return effect, control
    second = increment_body(b)
    if second is None:
        return None
    if second[1] == 1:
        return None  # This would restart the node; no termination proof here.
    return add_vectors(effect, second[0]), max(second[1] - 1, 0)


@lru_cache(None)
def total_affine(term):
    """Certified total affine map for increments, transfers and compositions."""
    if term[0] == 'L':
        op, *args = term[1]
        if op != 'I':
            return None
        assert 0 <= args[0] < 9
        result = [list(row) for row in identity()]
        result[args[0]][9] = 1
        return tuple(map(tuple, result))
    if term[0] == 'S':
        result = identity()
        for child in term[1]:
            following = total_affine(child)
            if following is None:
                return None
            result = multiply(following, result)
        return result
    a, b = term[1:]
    if a[0] != 'L' or a[1][0] != 'D':
        return None
    source = a[1][1]
    body = increment_body(b)
    if body is None or body[1] != 1 or body[0][source] != 0:
        return None
    result = [list(row) for row in identity()]
    result[source] = [0] * 10
    for j, amount in enumerate(body[0]):
        if j != source:
            result[j][source] += amount
    return tuple(map(tuple, result))


class Normalizer:
    def __init__(self, decoder, allow_affine=False):
        self.decoder = decoder
        self.allow_affine = allow_affine
        self.swaps = Counter()
        self.sequence_nodes = 0
        self.dependent_pairs = 0
        self.maximum_sequence_length = 0

    @lru_cache(None)
    def independence(self, a, b):
        if a == b:
            return None
        fa, ha = summary(a)
        fb, hb = summary(b)
        if ha or hb:
            return None
        if fa.isdisjoint(fb):
            return 'disjoint_footprints'
        if self.allow_affine:
            ma, mb = total_affine(a), total_affine(b)
            if ma is not None and mb is not None and multiply(ma, mb) == multiply(mb, ma):
                return 'certified_total_affine_maps'
        return None

    @lru_cache(None)
    def word(self, word):
        self.sequence_nodes += 1
        self.maximum_sequence_length = max(self.maximum_sequence_length, len(word))
        successors = [[] for _ in word]
        degree = [0] * len(word)
        for j in range(len(word)):
            for i in range(j):
                if self.independence(word[i], word[j]) is None:
                    successors[i].append(j)
                    degree[j] += 1
                    self.dependent_pairs += 1
        ready = [(word[i], i) for i, n in enumerate(degree) if n == 0]
        heapq.heapify(ready)
        order = []
        while ready:
            _, i = heapq.heappop(ready)
            order.append(i)
            for j in successors[i]:
                degree[j] -= 1
                if degree[j] == 0:
                    heapq.heappush(ready, (word[j], j))
        assert len(order) == len(word)
        # Do not trust even our dependency-graph construction alone: verify
        # the explicit adjacent swaps converting the input to this ordering.
        current = list(range(len(word)))
        for position, wanted in enumerate(order):
            at = current.index(wanted, position)
            while at > position:
                left, right = current[at - 1], current[at]
                rule = self.independence(word[left], word[right])
                assert rule is not None, 'A dependent atom would be exchanged'
                self.swaps[rule] += 1
                current[at - 1], current[at] = right, left
                at -= 1
        assert current == order
        return tuple(word[i] for i in order)

    @lru_cache(None)
    def edge(self, e):
        if e[0] != 'N':
            return ('L', e)
        a, b = self.decoder.nodes[e[1]]
        aa, bb = self.edge(a), self.edge(b)
        if self.decoder.bounds(a) == self.decoder.bounds(b) == (0, 0):
            left = aa[1] if aa[0] == 'S' else (aa,)
            right = bb[1] if bb[0] == 'S' else (bb,)
            return ('S', self.word(left + right))
        return ('A', aa, bb)

    def result(self):
        term = self.edge(('N', self.decoder.root))
        return term, {
            'normal_form_sha256': hashlib.sha256(encode(term)).hexdigest(),
            'closed_sequence_words_normalized': self.sequence_nodes,
            'maximum_sequence_length': self.maximum_sequence_length,
            'dependent_pairs_explicitly_built': self.dependent_pairs,
            'adjacent_swaps_individually_checked': dict(self.swaps),
            'total_affine_mode': self.allow_affine,
        }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('candidates', nargs='+', type=Path)
    ap.add_argument('--baseline', type=Path, default=BASE)
    ap.add_argument('--literal', type=Path, default=LITERAL)
    ap.add_argument('--allow-affine', action='store_true')
    ap.add_argument('--output', type=Path, default=Path(__file__).with_name('trace_reassociation_audit.json'))
    a = ap.parse_args()
    if not __debug__:
        ap.error('Assertions must be enabled')
    nodes, root, baseline_hash = read_json(a.baseline)
    baseline = Decoder(nodes, root)
    ln, lr = read_literal(a.literal)
    assert baseline.tree(('N', root)) == Decoder(ln, lr).tree(('N', lr))
    assert baseline.bounds(('N', root)) == (0, 0)
    old_term, old_report = Normalizer(baseline, a.allow_affine).result()
    results = []
    for path in a.candidates:
        cn, cr, ch = read_json(path)
        candidate = Decoder(cn, cr)
        assert len(candidate.reached) == len(cn)
        assert candidate.bounds(('N', cr)) == (0, 0)
        term, record = Normalizer(candidate, a.allow_affine).result()
        assert term == old_term, f'Complete source trace normal forms differ: {path}'
        record.update(file=path.name, file_sha256=ch, status='PASS',
                      source_nodes=len(cn), source_leaves=len(candidate.sites),
                      metrics=candidate.metrics())
        results.append(record)
    result = {'status': 'PASS', 'baseline_file_sha256': baseline_hash,
              'baseline': old_report, 'candidates': results,
              'scope': 'Finite source normal and halting semantics only. No binary-machine compiler, macro or bootstrap claim.'}
    a.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
