#!/usr/bin/env python3
"""Two exact tests of median decoding on synthetic multiplicity data.

The rows are fabricated nonnegative integer triples, not ordinates or measured
multiplicities of any L-function. Real and imaginary parts are rational.
"""

from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations, permutations
from math import factorial
from statistics import median


def inverse(matrix):
    n = len(matrix)
    augmented = [
        [Q(v) for v in row] + [Q(i == j) for j in range(n)]
        for i, row in enumerate(matrix)
    ]
    for col in range(n):
        pivot = next((i for i in range(col, n) if augmented[i][col]), None)
        if pivot is None:
            return None
        augmented[col], augmented[pivot] = augmented[pivot], augmented[col]
        divisor = augmented[col][col]
        augmented[col] = [v / divisor for v in augmented[col]]
        for i in range(n):
            if i != col:
                factor = augmented[i][col]
                augmented[i] = [x - factor * y for x, y in zip(augmented[i], augmented[col])]
    return [row[n:] for row in augmented]


def synthetic_rows():
    """Mix three directions and cyclically permute their coordinates."""
    rows = []
    for block in range(7):
        scale = 1 + block % 3
        directions = ((1, scale, 0), (0, 1, scale), (scale, 0, 1))
        order = list(permutations(range(3)))[block % 6]
        rows.extend(tuple(row[j] for j in order) for row in directions)
    return rows


def extract_bases(rows, dimension):
    available = list(range(len(rows)))
    blocks = []
    while len(available) >= dimension:
        for indices in combinations(available, dimension):
            inv = inverse([rows[i] for i in indices])
            if inv is not None:
                blocks.append((indices, inv))
                available = [i for i in available if i not in indices]
                break
        else:
            break
    return blocks, available


def multiply(matrix, vector):
    return [tuple(sum(a * z[j] for a, z in zip(row, vector)) for j in (0, 1))
            for row in matrix]


def build_estimates(blocks, baseline, spikes):
    estimates = []
    for indices, inv in blocks:
        table = {}
        for count in range(3):
            for hit in combinations(indices, count):
                observed = [tuple(baseline[i][j] + (spikes[i][j] if i in hit else 0)
                                  for j in (0, 1)) for i in indices]
                table[frozenset(hit)] = multiply(inv, observed)
        estimates.append(table)
    return estimates


def check_all_placements(blocks, samples, spikes, truth, error_radius):
    # Enumerate 1 erasure and 2 corruptions among all rows. The values at
    # corrupted rows are displaced far beyond the small noise budget.
    tables = build_estimates(blocks, samples, spikes)
    worst_squared = Q(0)
    cases = 0
    for bad in combinations(range(len(samples)), 2):
        bad = frozenset(bad)
        local = [table[bad.intersection(indices)] for (indices, _), table in zip(blocks, tables)]
        for erased_block, (indices, _) in enumerate(blocks):
            # Erasing any row of this basis discards this whole candidate.
            multiplicity = len(set(indices) - bad)
            if not multiplicity:
                continue
            retained = local[:erased_block] + local[erased_block + 1:]
            errors = []
            for k, value in enumerate(truth):
                estimate = [median(candidate[k][part] for candidate in retained) for part in (0, 1)]
                errors.append(sum((x - y)**2 for x, y in zip(estimate, value)))
            worst_squared = max(worst_squared, *errors)
            assert max(errors) <= 2 * error_radius**2
            cases += multiplicity
    return cases, worst_squared


def check_disjoint_example(truth):
    rows = synthetic_rows()
    blocks, unused = extract_bases(rows, len(truth))
    assert not unused and len(blocks) == 7
    assert sorted(i for indices, _ in blocks for i in indices) == list(range(len(rows)))
    largest_entry = max(max(row) for row in rows)
    kappa = max(sum(abs(v) for v in row) for _, inv in blocks for row in inv)
    cofactor_bound = factorial(len(truth)) * largest_entry**(len(truth) - 1)
    assert kappa <= cofactor_bound
    eps = Q(1, 100)
    clean = multiply(rows, truth)
    # Every error has Euclidean modulus exactly eps (the 3-4-5 triangle).
    noise = [(eps * Q(3, 5) * (-1)**(i // 2), eps * Q(4, 5) * (-1)**(i // 3))
             for i in range(len(rows))]
    assert all(x*x + y*y == eps*eps for x, y in noise)
    noisy = [(x + u, y + v) for (x, y), (u, v) in zip(clean, noise)]
    spikes = [(Q(99 + i) * (-1)**(i % 3), Q(123 - i) * (-1)**(i // 2))
              for i in range(len(rows))]
    print("Alternative decoder: disjoint bases, then medians of estimates.")
    print(f"Rows={len(rows)}, dimension={len(truth)}, disjoint bases={len(blocks)}, "
          f"maximum integer entry={largest_entry}.")
    print(f"Maximum inverse row-sum norm={kappa}; uniform cofactor bound={cofactor_bound}.")
    print("2 corruptions and 1 erasure; 2*2+1 < 7.")
    for label, samples, noise_level in (("Exact background", clean, Q(0)),
                                       ("Noisy background", noisy, eps)):
        cases, worst_squared = check_all_placements(blocks, samples, spikes, truth,
                                                   kappa * noise_level)
        assert cases == 3990
        print(f"{label}: {cases} placements, maximum squared complex coordinate error "
              f"{worst_squared}, bound {2 * (kappa * noise_level)**2}.")


def frequent_independent_rows(rows):
    """Scan by calibrated frequency, keeping only rank-increasing row types."""
    counts = Counter(rows)
    dimension = len(rows[0])
    selected = []
    skipped = []
    for row in sorted(counts, key=lambda r: (-counts[r], r)):
        candidate = selected + [row]
        minors = combinations(range(dimension), len(candidate))
        if any(inverse([[r[j] for j in cols] for r in candidate]) is not None for cols in minors):
            selected = candidate
        else:
            skipped.append(row)
        if len(selected) == dimension:
            break
    assert len(selected) == dimension
    return selected, skipped


def frequent_error_range(rows, selected, truth, eps):
    groups = [tuple(i for i, row in enumerate(rows) if row == key) for key in selected]
    group_sets = [frozenset(indices) for indices in groups]
    clean = multiply(rows, truth)
    # Nonconstant clean background errors have Euclidean norm eps.
    noise = [(eps * Q(3, 5) * (-1)**(i // 2), eps * Q(4, 5) * (-1)**(i // 3))
             for i in range(len(rows))]
    samples = [(x + dx, y + dy) for (x, y), (dx, dy) in zip(clean, noise)]
    inv = inverse(selected)
    assert inv is not None

    @lru_cache(maxsize=None)
    def projection_median(group, hit, missing):
        values = []
        for i in groups[group]:
            if i == missing:
                continue
            x, y = samples[i]
            if i in hit:
                x += (1000 + i) * (-1)**i
                y += (1200 - i) * (-1)**(i // 2)
            values.append((x, y))
        return tuple(median([z[j] for z in values]) for j in (0, 1))

    @lru_cache(maxsize=None)
    def squared_error(projections):
        estimate = multiply(inv, projections)
        return max(sum((x-y)**2 for x, y in zip(z, w)) for z, w in zip(estimate, truth))

    worst = Q(0)
    cases = 0
    for pair in combinations(range(len(rows)), 2):
        bad = frozenset(pair)
        hits = [bad.intersection(s) for s in group_sets]
        for erased in range(len(rows)):
            if erased in bad:
                continue
            projections = tuple(projection_median(j, hits[j], erased if erased in s else -1)
                                for j, s in enumerate(group_sets))
            worst = max(worst, squared_error(projections))
            cases += 1
    return cases, worst


def check_frequent_example(truth):
    frequencies = [
        ((1, 1, 0), 11), ((2, 2, 0), 10), ((2, 1, 1), 9),
        ((1, 0, 2), 8), ((0, 0, 1), 1)
    ]
    # Interleave the row types so their frequencies must be recovered.
    rows = [row for j in range(max(n for _, n in frequencies)) for row, n in frequencies if j < n]
    selected, skipped = frequent_independent_rows(rows)
    assert selected == [(1, 1, 0), (2, 1, 1), (1, 0, 2)]
    assert skipped == [(2, 2, 0)]
    assert rows.count((0, 0, 1)) == 1 and (0, 0, 1) not in selected
    kappa = max(sum(abs(x) for x in row) for row in inverse(selected))
    print("Primary decoder: median within each frequent type, then one linear solve.")
    print(f"Rows={len(rows)}, selected integer rows with frequencies "
          f"{[(r, rows.count(r)) for r in selected]}.")
    print("Dependent type (2,2,0) has frequency 10 and is skipped; rare type (0,0,1) occurs once.")
    print(f"Selected matrix inverse row-sum norm={kappa}; 2*2+1 < minimum selected frequency 8.")
    for label, eps in (("Exact background", Q(0)), ("Noisy background", Q(1, 100))):
        cases, worst = frequent_error_range(rows, selected, truth, eps)
        bound = 2 * (kappa * eps)**2
        assert cases == 27417 and worst <= bound
        print(f"{label}: {cases} placements, maximum squared complex coordinate error "
              f"{worst}, bound {bound}.")


def main():
    if not __debug__:
        raise SystemExit("Use ordinary Python with assertions enabled.")
    truth = [(Q(7, 5), Q(2, 11)), (-Q(11, 6), Q(4, 9)), (Q(4, 3), -Q(7, 8))]
    print("Synthetic models; no L-function zeros are used.")
    check_frequent_example(truth)
    check_disjoint_example(truth)
    print("All rational checks passed.")


if __name__ == "__main__":
    main()
