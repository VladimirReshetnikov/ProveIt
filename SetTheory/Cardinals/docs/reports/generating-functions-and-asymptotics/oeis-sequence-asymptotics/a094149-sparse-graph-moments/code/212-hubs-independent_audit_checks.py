#!/usr/bin/env python3
"""Independent finite checks for Report212. Uses only the Python standard library.

Run from any directory; default input is the complete k<=32 fixture.
Enumeration generates tree walks directly, rather than via either audited recurrence.
"""
from collections import Counter
from fractions import Fraction
from math import comb
from pathlib import Path
import json
import argparse

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
from common import load_rows
CHECKS = ('hub_bound', 'rotation', 'double_hub', 'first_edge', 'partition_cut',
          'stored_small_rows', 'stored_completeness', 'stored_row_sum', 'ratio_decrease')
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--inject-failure', choices=CHECKS,
                    help='Deliberately corrupt one value before its named comparison.')
parser.add_argument('--data-dir', type=Path, default=ROOT/'data'/'fixture32',
                    help='Directory containing stored C++ TSV files; no recurrence is regenerated here.')
parser.add_argument('--expected-max', type=int, default=32)
parser.add_argument('--data-kind', choices=('fixture','fresh-generation','stored'), default='fixture')
parser.add_argument('--output', type=Path, default=ROOT/'build'/'audit_checks.json')
args = parser.parse_args()


def require(condition, check, context=None):
    if not condition:
        raise RuntimeError(f'CHECK_FAILED[{check}]: {context!r}')


def corrupt_number(value, check):
    return value + 1 if args.inject_failure == check else value


N = 8
F = [Counter({0: 1})]
results = {
    'enumeration_method': 'Follow an existing adjacent edge or discover one fresh vertex; normalize by first occurrence; close at vertex zero.',
    'maximum_enumerated_half_length': N,
    'root_departure_rows': [],
    'rotation_checks': [],
    'guard_mode': 'Explicit runtime guards; no optimization-sensitive assertion statements.',
    'verification_scope': {'direct_walk_enumeration_and_both_recursions_max_k': N, 'input_kind': args.data_kind, 'higher_rows_are_read_and_consistency_checked_not_independently_regenerated': True},
}
for k in range(1, N + 1):
    adjacency, departures, depth = [[]], [0], [0]
    row, hub_sum, covered, double = Counter(), Counter(), Counter(), Counter()

    def enumerate_walks(cur, step):
        if step == 2 * k:
            if cur:
                return
            row[departures[0]] += 1
            for threshold in range(k // 2 + 1, k + 1):
                h = sum(d >= threshold for d in departures)
                checked_h = 3 if args.inject_failure == "hub_bound" else h
                require(checked_h <= 2, "hub_bound", (k, threshold, checked_h))
                hub_sum[threshold] += h
                covered[threshold] += h > 0
                double[threshold] += h == 2
            return
        remaining = 2 * k - step
        if depth[cur] > remaining or (depth[cur] - remaining) % 2:
            return
        departures[cur] += 1
        for nxt in adjacency[cur]:
            enumerate_walks(nxt, step + 1)
        if depth[cur] + 1 <= remaining - 1:
            nxt = len(adjacency)
            adjacency[cur].append(nxt)
            adjacency.append([cur])
            departures.append(0)
            depth.append(depth[cur] + 1)
            enumerate_walks(nxt, step + 1)
            adjacency[cur].pop()
            adjacency.pop()
            departures.pop()
            depth.pop()
        departures[cur] -= 1

    enumerate_walks(0, 0)
    F.append(row)
    results['root_departure_rows'].append({
        'k': k, 'F_k_1_through_k': [row[m] for m in range(1, k + 1)],
        'M_2k': sum(row.values()),
    })
    for threshold in range(k // 2 + 1, k + 1):
        weighted = sum(Fraction(2 * k, m) * count for m, count in row.items() if m >= threshold)
        checked_weighted = corrupt_number(weighted, "rotation")
        require(checked_weighted == hub_sum[threshold] == covered[threshold] + double[threshold],
                "rotation", (k, threshold, checked_weighted, hub_sum[threshold], covered[threshold], double[threshold]))
        results['rotation_checks'].append({
            'k': k, 'threshold': threshold,
            'weighted_root_sum': str(weighted),
            'qualifying_walks': covered[threshold],
            'double_hub_walks': double[threshold],
        })


def E(t, q):
    return sum(count * comb(j + q - 1, q - 1) for j, count in F[t].items())


# Exact double-hub refinement: first step crosses the unique central edge.
def Ehat(a, q, threshold):
    minimum = max(0, threshold - q)
    return sum(count * comb(j + q - 1, q - 1)
               for j, count in F[a].items() if j >= minimum)


for check in results['rotation_checks']:
    k, threshold = check['k'], check['threshold']
    candidate = sum(
        Fraction(k, q) * sum(
            Ehat(a, q, threshold) * Ehat(k - q - a, q, threshold)
            for a in range(k - q + 1)
        ) for q in range(1, k + 1)
    )
    checked_candidate = corrupt_number(candidate, 'double_hub')
    require(checked_candidate == check['double_hub_walks'], 'double_hub',
            (k, threshold, checked_candidate, check['double_hub_walks']))
    check['exact_double_hub_formula'] = str(candidate)
results['exact_double_hub_formula_cases_passed'] = len(results['rotation_checks'])


first_edge_checks = 0
for k in range(1, N + 1):
    for m in range(1, k + 1):
        candidate = sum(
            comb(m - 1, q - 1) * sum(
                E(a, q) * F[k - q - a].get(m - q, 0)
                for a in range(k - q + 1)
            ) for q in range(1, m + 1)
        )
        checked_candidate = corrupt_number(candidate, 'first_edge')
        require(checked_candidate == F[k][m], 'first_edge', (k, m, checked_candidate, F[k][m]))
        first_edge_checks += 1


def partition_block_sizes(n):
    """Yield once per set partition, via restricted-growth labels."""
    def visit(left, sizes):
        if not left:
            yield tuple(sizes)
            return
        for i in range(len(sizes)):
            sizes[i] += 1
            yield from visit(left - 1, sizes)
            sizes[i] -= 1
        sizes.append(1)
        yield from visit(left - 1, sizes)
        sizes.pop()
    yield from visit(n, [])


branch_checks = 0
for k in range(1, N + 1):
    for n in range(1, k + 1):
        s, candidate = k - n, 0
        for sizes in partition_block_sizes(n):
            coefficients = [1] + [0] * s
            for q in sizes:
                coefficients = [
                    sum(coefficients[j] * E(t - j, q) for j in range(t + 1))
                    for t in range(s + 1)
                ]
            candidate += coefficients[s]
        checked_candidate = corrupt_number(candidate, 'partition_cut')
        require(checked_candidate == F[k][n], 'partition_cut', (k, n, checked_candidate, F[k][n]))
        branch_checks += 1

results['first_edge_recurrence_cases_passed'] = first_edge_checks
results['partition_cut_formula_cases_passed'] = branch_checks
results['rotation_identity_cases_passed'] = len(results['rotation_checks'])

# Compare independent small rows with the separate C++/GMP output.
moments, stored = load_rows(args.data_dir, args.expected_max)
stored.pop(0)
for k in range(1, N + 1):
    checked_row = dict(stored[k])
    if args.inject_failure == 'stored_small_rows':
        checked_row[1] = checked_row.get(1, 0) + 1
    require(checked_row == dict(F[k]), 'stored_small_rows', (k, checked_row, dict(F[k])))
results['independent_small_rows_match_cpp_output'] = True

stored_max = max(moments)
checked_root_keys = set(stored)
if args.inject_failure == 'stored_completeness':
    checked_root_keys.discard(stored_max)
require(set(moments) == set(range(stored_max + 1))
        and moments.get(0) == 1
        and checked_root_keys == set(range(1, stored_max + 1))
        and all(set(stored[k]) == set(range(1, k + 1)) for k in stored),
        'stored_completeness', {'moment_max': stored_max,
            'moment_rows': len(moments), 'root_rows_checked': len(checked_root_keys)})
results['stored_moment_and_root_key_sets_complete'] = True
for k, row in stored.items():
    checked_sum = corrupt_number(sum(row.values()), 'stored_row_sum')
    require(checked_sum == moments[k], 'stored_row_sum', (k, checked_sum, moments[k]))
results['stored_root_rows_sum_to_stored_moments'] = True
results['verification_scope']['stored_consistency_max_k'] = max(moments)

# Verify the finite-ratio description, using exact rational comparisons.
B = [1]
for n in range(max(moments) + 1):
    B.append(sum(comb(n, j) * B[j] for j in range(n + 1)))
ratios = [(k, Fraction(moment, 2 * B[k + 1])) for k, moment in sorted(moments.items())]
peak_index = max(range(len(ratios)), key=lambda i: ratios[i][1])
checked_ratios = list(ratios)
if args.inject_failure == 'ratio_decrease':
    require(peak_index + 1 < len(checked_ratios), 'failure_injection_setup', peak_index)
    next_k = checked_ratios[peak_index + 1][0]
    checked_ratios[peak_index + 1] = (next_k, checked_ratios[peak_index][1] + 1)
require(all(checked_ratios[i + 1][1] < checked_ratios[i][1]
            for i in range(peak_index, len(checked_ratios) - 1)), 'ratio_decrease', peak_index)
results['stored_moment_ratio_check'] = {
    'peak_k': ratios[peak_index][0],
    'peak_ratio_approximate': float(ratios[peak_index][1]),
    'final_k': ratios[-1][0],
    'final_ratio_approximate': float(ratios[-1][1]),
    'strictly_decreasing_after_peak_in_computed_range': True,
    'comparison_method': 'Exact fractions; floating-point values shown only for display.',
}
results['all_checks_passed'] = True
out = args.output
out.parent.mkdir(parents=True,exist_ok=True)
out.write_text(json.dumps(results, indent=2) + '\n')
print(json.dumps({
    'all_checks_passed': True,
    'enumeration_max_k': N,
    'first_edge_cases': first_edge_checks,
    'partition_cut_cases': branch_checks,
    'rotation_cases': len(results['rotation_checks']),
    'exact_double_hub_cases': len(results['rotation_checks']),
    'result_file': str(out),
}, indent=2))
