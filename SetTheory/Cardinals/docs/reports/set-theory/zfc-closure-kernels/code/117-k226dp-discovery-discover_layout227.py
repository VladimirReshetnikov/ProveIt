#!/usr/bin/env python3
"""Reproduce the fixed 49-atom dynamic-programming layout discovery.

The input is a finite constrained ordered-tree problem. Its feasibility masks
record the source decoder's discovery constraints; they are not proof premises.
reconstruct227.py replays the literal answer, and the independent unbounded
runtime certificate checks the resulting machine for all counter values.
"""
from functools import cache
from pathlib import Path
import argparse
import hashlib
import json


def append(context, bit):
    suffix, zeros = context
    return (suffix + bit)[-2:], zeros + 1 if bit == '0' else 0


def solve(problem):
    atoms = problem['atoms']
    weights = [atom['leaves'] for atom in atoms]
    feasible = [{tuple(context) for context in atom['feasible_contexts']} for atom in atoms]
    prefix = [0]
    for w in weights:
        prefix.append(prefix[-1] + w)
    @cache
    def dp(first, end, contexts):
        if any(zeros > 6 for suffix, zeros in contexts):
            return None
        if end == first + 1:
            return (0, first) if all(c in feasible[first] for c in contexts) else None
        left_contexts = tuple(sorted({append(c, '0') for c in contexts}))
        right_contexts = tuple(sorted({append(c, '1') for c in contexts}))
        best = None
        for middle in range(first + 1, end):
            left = dp(first, middle, left_contexts)
            if left is None:
                continue
            right = dp(middle, end, right_contexts)
            if right is None:
                continue
            cost = left[0] + right[0] + prefix[end] - prefix[first]
            if best is None or cost < best[0]:
                best = cost, (left[1], right[1])
        return best
    contexts = tuple(sorted(tuple(c) for c in problem['root_contexts']))
    answer = dp(0, len(atoms), contexts)
    if answer is None:
        raise ValueError('No feasible ordered binary tree')
    cost, pattern = answer
    pattern = json.loads(json.dumps(pattern))
    if cost != problem['expected_objective'] or pattern != problem['expected_pattern']:
        raise ValueError('Optimum differs from the recorded layout')
    return {'status': 'PASS_REPRODUCED_ORDERED_LAYOUT', 'atom_count': len(atoms),
            'instruction_occurrences': sum(weights), 'old_objective': problem['old_objective'],
            'new_objective': cost, 'pattern': pattern, 'cached_subproblems': dp.cache_info().currsize,
            'claim': 'Exact optimum for the supplied fixed atom sequence, feasibility masks and weighted-depth objective; no global state minimality claim.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--problem', type=Path, default=Path(__file__).with_name('layout_problem227.json'))
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    raw = args.problem.read_bytes()
    result = solve(json.loads(raw))
    result['problem_sha256'] = hashlib.sha256(raw).hexdigest()
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'pattern'}, indent=2))
