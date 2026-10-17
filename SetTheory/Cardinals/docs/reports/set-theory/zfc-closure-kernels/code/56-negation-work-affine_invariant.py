#!/usr/bin/env python3
"""Exact affine register invariants for the pinned 252-state source program.

This computes rational affine hulls using primitive integer row bases. All
results concern the register program, not a new binary machine. A separate
postfix certificate is emitted, so worklist order is not part of the argument.
"""
from __future__ import annotations

import argparse
from collections import Counter, deque
from functools import reduce
from math import gcd
import hashlib
import json
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
REPO = HERE.parent / 'source/ProveIt'
BASE = REPO / 'Computability/BusyBeaver/Research/ZFC'
sys.path.insert(0, str(BASE))
import permutation252_phase_analysis as phase

DIM = 10


def primitive(v):
    v = tuple(v)
    g = reduce(gcd, v, 0)
    if not g:
        return v
    p = next(x for x in v if x)
    g = g if p > 0 else -g
    return tuple(x // g for x in v)


def pivot(v):
    return next(i for i, x in enumerate(v) if x)


def basis(vectors):
    """Canonical reduced row basis; each row has coprime integer entries."""
    out = []
    for row in vectors:
        v = primitive(row)
        for b in out:
            p = pivot(b)
            if v[p]:
                v = primitive(b[p] * x - v[p] * y for x, y in zip(v, b))
        if not any(v):
            continue
        p = pivot(v)
        new = []
        for b in out:
            if b[p]:
                b = primitive(v[p] * x - b[p] * y for x, y in zip(b, v))
            new.append(b)
        new.append(v)
        out = sorted(new, key=pivot)
    return tuple(out)


def constrain(space, equation):
    vals = [sum(a * b for a, b in zip(v, equation)) for v in space]
    i = next((i for i, v in enumerate(vals) if v), None)
    if i is None:
        return space
    answer = basis(tuple(vals[i] * a - vals[j] * b for a, b in zip(v, space[i]))
                   for j, v in enumerate(space) if j != i)
    return answer if any(v[0] for v in answer) else ()


def coordinate(space, register, value):
    eq = [0] * DIM
    eq[0], eq[register + 1] = -value, 1
    return constrain(space, eq)


def equations(space):
    if not space:
        return ()
    pivots = {pivot(row) for row in space}
    answer = []
    for j in range(DIM):
        if j in pivots:
            continue
        den = 1
        for row in space:
            den = den * row[pivot(row)] // gcd(den, row[pivot(row)])
        eq = [0] * DIM
        eq[j] = den
        for row in space:
            eq[pivot(row)] = -row[j] * (den // row[pivot(row)])
        answer.append(primitive(eq))
    return basis(answer)


def reduce_naturals(space, masks):
    """Sound reductions using fixed zero/one masks and nonnegative equations."""
    if not space:
        return ()
    for i, m in enumerate(masks):
        if m in (1, 2):
            space = coordinate(space, i, m - 1)
            if not space:
                return ()
    while space:
        zeros = set()
        for eq0 in equations(space):
            eq = eq0
            coeff = eq[1:]
            if all(x <= 0 for x in coeff):
                eq = tuple(-x for x in eq)
            if not all(x >= 0 for x in eq[1:]):
                continue
            if eq[0] > 0:
                return ()
            # c_i*x_i <= -a_0: for naturals, a positive coefficient larger
            # than the right hand side forces x_i = 0.
            zeros.update(i for i, c in enumerate(eq[1:]) if c > -eq[0])
        new = space
        for i in sorted(zeros):
            new = coordinate(new, i, 0)
        if new == space:
            return space
        space = new
    return ()


def transfer(space, case, masks):
    if not space:
        return ()
    _, _, op, register, zero = case
    if op == 'CD':
        if zero:
            if not masks[register] & 1:
                return ()
            space = coordinate(space, register, 0)
        else:
            if not masks[register] & 6 or all(v[register + 1] == 0 for v in space):
                return ()
            # If r is an exact constant below one, the positive guard is false.
            first = next(v for v in space if v[0])
            a, d = first[register + 1], first[0]
            if a < d and all(v[register + 1] * d == v[0] * a for v in space):
                return ()
    if not space:
        return ()
    if op == 'CI' or op == 'CD' and not zero:
        delta = 1 if op == 'CI' else -1
        space = basis(tuple(x + delta * v[0] if j == register + 1 else x
                            for j, x in enumerate(v)) for v in space)
    return space


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, default=HERE / 'affine-invariants.json')
    ap.add_argument('--mode', choices=['linear', 'natural'], default='natural')
    args = ap.parse_args()
    begun = time.monotonic()
    raw = (REPO / 'lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v').read_bytes()
    assert hashlib.sha256(raw).hexdigest() == phase.PROG_SHA
    sites, cases, targets, first = phase.program_graph(raw)
    masks, enabled, _, _ = phase.phase_analysis(sites, cases, targets, first)
    outgoing = [[] for _ in sites]
    for i, case in enumerate(cases):
        outgoing[case[0]].append(i)
    values = [()] * len(sites)
    values[first] = ((1,) + (0,) * 9,)
    queue = deque([first])
    queued = {first}
    pops = 0
    updates = 0
    while queue:
        site = queue.popleft()
        queued.remove(site)
        pops += 1
        for i in outgoing[site]:
            target = targets[i]
            if target is None or not enabled[i]:
                continue
            val = transfer(values[site], cases[i], masks[site])
            if not val:
                continue
            if args.mode == 'natural':
                val = reduce_naturals(val, masks[target])
            if not val:
                continue
            old = values[target]
            new = basis(old + val)
            if new == old:
                continue
            assert len(new) > len(old) or not old
            values[target] = new
            updates += 1
            if target not in queued:
                queue.append(target)
                queued.add(target)
        if pops % 10000 == 0:
            print(json.dumps({'pops': pops, 'queue': len(queue), 'updates': updates,
                              'seconds': round(time.monotonic() - begun, 2)}), flush=True)
    possible = []
    for i, case in enumerate(cases):
        val = transfer(values[case[0]], case, masks[case[0]]) if values[case[0]] else ()
        target = targets[i]
        if val and target is not None:
            if args.mode == 'natural':
                val = reduce_naturals(val, masks[target])
            assert basis(values[target] + val) == values[target], ('not inductive', i)
        possible.append(bool(val))
    excluded = [i for i, p in enumerate(possible) if not p]
    affine_eqs = [equations(s) for s in values]
    result = {
        'status': 'inductive_affine_certificate', 'mode': args.mode,
        'source_sha256': phase.PROG_SHA,
        'scope': 'Register-program invariant from all-zero registers; no new binary machine.',
        'old_excluded_cases': phase.EXCLUDED, 'excluded_cases': excluded,
        'new_excluded_cases': [i for i in excluded if i not in phase.EXCLUDED],
        'possible_sites': sum(bool(s) for s in values),
        'pops': pops, 'updates': updates, 'seconds': time.monotonic() - begun,
        'rank_histogram': dict(Counter(len(s) for s in values)),
        'spaces': values, 'equations': affine_eqs,
        'case_possible': possible,
        'cases': cases, 'targets': targets,
        'site_masks': masks,
    }
    args.output.write_text(json.dumps(result, separators=(',', ':')) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in
                      ['spaces', 'equations', 'cases', 'targets', 'site_masks', 'case_possible']}, indent=2))


if __name__ == '__main__':
    main()
