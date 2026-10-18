#!/usr/bin/env python3
"""Sound difference-bound invariant for the literal nine-register source.

The interpreter graph is read by the already audited Prog254 path decoder.
The abstract carrier is a closed 10 x 10 difference-bound matrix: variable
zero is fixed zero and variables 1..9 are natural-valued registers. A row
entry D[i,j] means x_i-x_j <= D[i,j]. Increment/decrement are exact affine
updates, each decrement branch intersects with its exact guard, and Floyd
closure detects empty guards. Extrapolation at joins discards upper bounds
larger than --threshold, ensuring a finite ascending search. The emitted
invariant is checked independently of extrapolation by all exact transfer
inclusions. No bound on the concrete register values or run length is used.

This is a source-program invariant, not a proof that a mutated binary table
simulates that program. It changes no machine row.
"""
from __future__ import annotations

import argparse
from collections import deque
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
import time

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'upstream/Computability/BusyBeaver/Research/ZFC'
PROG = ROOT / 'upstream/lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v'
sys.path.insert(0, str(BASE))
import permutation252_phase_analysis as phase

N = 10
INF = 1_000_000


def close(matrix):
    result = matrix.copy()
    for k in range(N):
        # Do not turn infinity plus a negative finite bound into a finite one.
        a, b = result[:, k:k+1], result[k:k+1, :]
        candidate = np.where((a >= INF) | (b >= INF), INF, a + b)
        np.minimum(result, candidate, out=result)
    if np.any(result.diagonal() < 0):
        return None
    return result


def step(matrix, case):
    _, _, op, register, zero = case
    if matrix is None:
        return None
    result = matrix.copy()
    index = None if register is None else register + 1
    if op == 'CD':
        if zero:
            result[index, 0] = min(result[index, 0], 0)
        else:
            result[0, index] = min(result[0, index], -1)
        result = close(result)
        if result is None:
            return None
    if op == 'CI' or (op == 'CD' and not zero):
        amount = 1 if op == 'CI' else -1
        for j in range(N):
            if j != index:
                if result[index, j] < INF:
                    result[index, j] += amount
                if result[j, index] < INF:
                    result[j, index] -= amount
    return result


def extrapolate(matrix, threshold):
    result = matrix.copy()
    result[result > threshold] = INF
    return close(result)


def analyze(threshold):
    started = time.monotonic()
    raw = PROG.read_bytes()
    assert sha256(raw).hexdigest() == phase.PROG_SHA
    sites, cases, targets, first = phase.program_graph(raw)
    by_site = [[] for _ in sites]
    for index, case in enumerate(cases):
        by_site[case[0]].append(index)
    states = [None] * len(sites)
    states[first] = np.zeros((N, N), dtype=np.int64)
    worklist = deque([first])
    pending = {first}
    pops = 0
    while worklist:
        site = worklist.popleft()
        pending.remove(site)
        pops += 1
        if pops % 100000 == 0:
            print(json.dumps({'progress': pops, 'pending': len(pending),
                              'seconds': round(time.monotonic() - started, 2)}),
                  flush=True)
        for case_index in by_site[site]:
            target = targets[case_index]
            if target is None:
                continue
            result = step(states[site], cases[case_index])
            if result is None:
                continue
            old = states[target]
            joined = extrapolate(result if old is None else np.maximum(old, result),
                                 threshold)
            assert joined is not None
            if old is None or not np.array_equal(old, joined):
                if old is not None:
                    assert np.all(old <= joined)
                states[target] = joined
                if target not in pending:
                    pending.add(target)
                    worklist.append(target)

    # Independent postfix check uses exact (unextrapolated) transfer.
    assert first == 0 and np.all(states[first] >= 0)
    checked, excluded = 0, []
    for index, (case, target) in enumerate(zip(cases, targets)):
        result = step(states[case[0]], case)
        if result is None:
            excluded.append(index)
        elif target is not None:
            assert states[target] is not None
            assert np.all(result <= states[target]), (index, target)
            checked += 1

    # Compact class representation is a certificate for an independent reader.
    classes, class_ids, seen = [], [], {}
    for value in states:
        key = None if value is None else tuple(map(int, value.reshape(-1)))
        if key not in seen:
            seen[key] = len(classes)
            classes.append(None if key is None else list(key))
        class_ids.append(seen[key])
    return {
        'status': 'PASS exact source-transfer postfix certificate',
        'source_commit': '43026ff42f0939f09b9e95495248cfadcad38e38',
        'program_sha256': sha256(raw).hexdigest(),
        'threshold': threshold, 'infinity_sentinel': INF,
        'variables': ['zero'] + ['R' + str(i) for i in range(9)],
        'source_sites': len(sites), 'source_guards': len(cases),
        'worklist_pops': pops, 'seconds': time.monotonic() - started,
        'excluded_guards': excluded,
        'new_excluded_guards': sorted(set(excluded) - set(phase.EXCLUDED)),
        'excluded_details': [dict(index=i, path=cases[i][1], operation=cases[i][2],
                                 register=cases[i][3], zero=cases[i][4])
                             for i in excluded],
        'exact_postfix_edges_checked': checked,
        'invariant_classes': classes, 'site_class_ids': class_ids,
        'scope': 'Natural registers unbounded; source invariant only; no binary reduction.'
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--threshold', type=int, default=2)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    assert args.threshold >= 0
    report = analyze(args.threshold)
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: report[k] for k in ('threshold', 'worklist_pops', 'seconds',
                                           'excluded_guards', 'new_excluded_guards')},
                     indent=2), flush=True)


if __name__ == '__main__':
    main()
