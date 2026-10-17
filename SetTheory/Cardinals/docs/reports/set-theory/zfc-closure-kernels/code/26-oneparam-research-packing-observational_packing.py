#!/usr/bin/env python3
"""Finite checks for observational pairs and the EPSC pairing instance.

These checks audit finite relational structures. They do not prove consistency,
the infinite EPSC schema, a compiler simulation, or a small-machine record.
The accompanying report gives the general mathematical proofs.
"""
from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path


def structure(n, bits):
    rows = [(bits >> (i * n)) & ((1 << n) - 1) for i in range(n)]
    cols = [sum(((rows[i] >> j) & 1) << i for i in range(n)) for j in range(n)]
    obs = [sum((cols[i] == cols[j] and rows[i] == rows[j]) << j
               for j in range(n)) for i in range(n)]
    empties = sum((c == 0) << j for j, c in enumerate(cols))
    return rows, cols, obs, empties


def members(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def audits(max_n=4):
    counts = Counter()
    nontrivial_op = None
    profile_counterexample = None
    for n in range(1, max_n + 1):
        for bits in range(1 << (n * n)):
            rows, cols, obs, empties = structure(n, bits)
            counts['graphs'] += 1
            # An independent check of congruence in BOTH argument positions.
            for a in range(n):
                for b in members(obs[a]):
                    for z in range(n):
                        if (((rows[a] >> z) & 1) != ((rows[b] >> z) & 1)
                                or ((rows[z] >> a) & 1) != ((rows[z] >> b) & 1)):
                            raise AssertionError('observational congruence failed')
                        counts['atomic_congruence_comparisons'] += 1
                for b in range(n):
                    if cols[a] == cols[b] and rows[a] != rows[b] and profile_counterexample is None:
                        z = next(z for z in range(n)
                                 if ((rows[a] >> z) & 1) != ((rows[b] >> z) & 1))
                        profile_counterexample = dict(n=n, bits=bits, a=a, b=b, z=z,
                                                      rows=rows, columns=cols)
            # Pair(s,a,b) is the exact extension O(-,a) union O(-,b).
            extensions = {}
            for c, column in enumerate(cols):
                extensions.setdefault(column, []).append(c)
            # A local O-singleton of a is already enough to collapse the
            # outgoing inclusion U(a,b) to full observational equivalence.
            for a in range(n):
                if extensions.get(obs[a]):
                    for b in range(n):
                        outgoing_inclusion = rows[a] & ~rows[b] == 0
                        observational = bool(obs[a] & (1 << b))
                        if outgoing_inclusion != observational:
                            raise AssertionError('U differs from O despite an O-singleton witness')
                        counts['short_profile_singleton_checks'] += 1
            decoded = {}
            for a in range(n):
                for b in range(n):
                    target = obs[a] | obs[b]
                    # The displayed two-parameter matrix has one of two fibers.
                    initial = obs[a] | (obs[b] if empties & (1 << a) else 0)
                    subsequent = obs[b]
                    fiber_union = ((initial if empties else 0) |
                                   (subsequent if empties != (1 << n) - 1 else 0))
                    # Explicit local bound choices, checked as raw inclusions.
                    for x in range(n):
                        is_empty = bool(empties & (1 << x))
                        outputs = initial if is_empty else subsequent
                        bound = (a if is_empty and not (empties & (1 << a)) else b)
                        for y in members(outputs):
                            if cols[y] & ~cols[bound]:
                                raise AssertionError('pair-matrix local bound failed')
                        counts['pair_matrix_local_bounds'] += 1
                    # Conditional theorem: an empty object and an EPSC hull
                    # for this matrix force its extension to be the exact pair.
                    if empties:
                        for c, column in enumerate(cols):
                            active = empties | column
                            image = ((initial if active & empties else 0) |
                                     (subsequent if active & ~empties else 0))
                            hull = (image & ~column == 0 and column & ~fiber_union == 0)
                            counts['pair_matrix_hull_candidates'] += 1
                            if hull:
                                counts['pair_matrix_hull_witnesses'] += 1
                                if column != target:
                                    raise AssertionError('EPSC hull was not an observational pair')
                    # Enumerate ALL local Kuratowski witnesses in this graph.
                    for s in extensions.get(obs[a], ()):
                        for u in extensions.get(target, ()):
                            for t in extensions.get(obs[s] | obs[u], ()):
                                counts['ordered_pair_witnesses'] += 1
                                # Endpoint recovery depends only on the incoming
                                # profile of the code, even if its outgoing
                                # profile differs. This also covers O-related
                                # tail codes in the nested-tuple induction.
                                old = decoded.setdefault(cols[t], (a, b))
                                if not (obs[a] & (1 << old[0]) and obs[b] & (1 << old[1])):
                                    raise AssertionError('Kuratowski endpoint injectivity failed')
                                if a != b and nontrivial_op is None:
                                    nontrivial_op = dict(n=n, bits=bits, a=a, b=b,
                                                         s=s, u=u, code=t, rows=rows)
                    counts['ordered_pair_parameter_pairs'] += 1
            counts['graphs_with_ordered_pair_codes'] += bool(decoded)
    if profile_counterexample is None:
        raise AssertionError('missing incoming-profile negative control')
    return dict(scope='finite diagnostics, not a proof of consistency or compilation',
                max_n=max_n, counts=dict(sorted(counts.items())),
                incoming_profile_counterexample=profile_counterexample,
                nontrivial_ordered_pair_witness=nontrivial_op,
                mathematical_theorems_claimed_by_test=False)


def hf_code(values):
    t = frozenset()
    for a in reversed(values):
        t = frozenset((frozenset((a,)), frozenset((a, t))))
    return t


def hf_audit():
    """Witness-rich checks, avoiding vacuous universal Pairing on finite sets."""
    from itertools import product
    e = frozenset()
    one = frozenset((e,))
    base = (e, one, frozenset((one,)), frozenset((e, one)))
    domain = set(base)
    by_length = {}
    for length in range(5):
        seen = {}
        for values in product(base, repeat=length):
            t = hf_code(values)
            if t in seen and seen[t] != values:
                raise AssertionError('tuple injection failed')
            seen[t] = values
            todo = [t]
            while todo:
                u = todo.pop()
                if u not in domain:
                    domain.add(u)
                    todo.extend(u)
        by_length[str(length)] = len(seen)
    # Clone every vertex twice, with all original edges between both clones.
    # The raw relation is nonextensional, and observational classes are exactly
    # the two clones. Check directly by incoming and outgoing bit profiles.
    def key(x):
        return repr(sorted((key(y) for y in x)))
    objects = sorted(domain, key=key)
    ids = {x: i for i, x in enumerate(objects)}
    n = len(objects) * 2
    columns = []
    for x in objects:
        m = sum(3 << (2 * ids[y]) for y in x)
        columns.extend((m, m))
    rows = [0] * n
    for j, col in enumerate(columns):
        for i in members(col):
            rows[i] |= 1 << j
    groups = {}
    for i, profiles in enumerate(zip(rows, columns)):
        groups.setdefault(profiles, []).append(i)
    if sorted(map(len, groups.values())) != [2] * len(objects):
        raise AssertionError('cloned HF observational quotient differs')
    return dict(tuple_codes_per_length=by_length, hf_objects=len(objects),
                raw_cloned_objects=n, observational_classes=len(groups),
                each_observational_class_size=2,
                explains_nonvacuity='Local code witnesses are constructed explicitly; no finite EPSC model is asserted.')


def main():
    if not __debug__:
        raise SystemExit('Run without Python optimization.')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--max-n', type=int, default=4, choices=range(1, 5))
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    result = audits(args.max_n)
    result['hereditarily_finite_tuple_controls'] = hf_audit()
    text = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
