#!/usr/bin/env python3
"""Exact, stdlib-only finite checks for bounded-multiplicity ascent sequences.

No correctness condition relies on Python's removable assertion statement.
The fixture schemas and required coverage are fixed here, not inferred from data.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from functools import lru_cache
from itertools import permutations, product
import json
from pathlib import Path
import sys

RS = tuple(range(2, 7))
N = 10
DATA = Path(__file__).resolve().parent / "data"


class VerificationError(RuntimeError):
    """A failed exact check, including invalid or incomplete reference data."""


def require(condition, message):
    if not condition:
        raise VerificationError(message)


def same(actual, expected, context):
    require(actual == expected, f"{context}: got {actual!r}; expected {expected!r}")


def integer(value, context, low=0, high=None):
    require(type(value) is int, f"{context}: integer required (booleans excluded)")
    require(value >= low, f"{context}: below minimum {low}")
    if high is not None:
        require(value <= high, f"{context}: above maximum {high}")
    return value


def exact_keys(value, keys, context):
    require(type(value) is dict, f"{context}: object required")
    same(set(value), set(keys), f"{context}: exact fields")


def array(value, context):
    require(type(value) is list, f"{context}: array required")
    return value


def no_duplicate_keys(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"JSON duplicate key: {key!r}")
        result[key] = value
    return result


def forbidden_constant(value):
    raise VerificationError(f"JSON nonfinite constant: {value}")


def load_json(path):
    try:
        with Path(path).open(encoding="utf-8") as stream:
            return json.load(stream, object_pairs_hook=no_duplicate_keys,
                             parse_constant=forbidden_constant)
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise VerificationError(f"Cannot read strict JSON {path}: {exc}") from exc


def validate_counts(document):
    exact_keys(document, ("schema_version", "coverage", "rows"), "counts")
    same(integer(document["schema_version"], "counts schema", 1), 1, "counts schema")
    coverage = document["coverage"]
    exact_keys(coverage, ("r_min", "r_max", "n_min", "n_max"), "counts coverage")
    for key, target in {"r_min": 2, "r_max": 6, "n_min": 0, "n_max": N}.items():
        same(integer(coverage[key], f"counts coverage {key}"), target, f"counts coverage {key}")
    result = {}
    for row in array(document["rows"], "count rows"):
        exact_keys(row, ("r", "values"), "count row")
        r = integer(row["r"], "count row r", 2, 6)
        require(r not in result, f"duplicate count row r={r}")
        values = array(row["values"], f"count values r={r}")
        same(len(values), N + 1, f"count coverage r={r}")
        for n, value in enumerate(values):
            integer(value, f"count r={r}, n={n}", 1)
        same(values[:2], [1, 1], f"empty/singleton counts r={r}")
        result[r] = values
    same(set(result), set(RS), "count r coverage")
    return result


def endpoint_statistics(r, n, x):
    """Recover (N_1,...,N_r, distinct, ascents) from a nonempty endpoint."""
    remainder = n - sum((r-j)*x[j-1] for j in range(1, r))
    require(remainder >= 0 and remainder % r == 0,
            f"endpoint r={r}, n={n}, x={x}: impossible used multiplicities")
    multiplicities = tuple(x[r-k-1] for k in range(1, r)) + (remainder // r,)
    distinct = sum(multiplicities)
    ascents = x[-1] + distinct - 2
    require(1 <= distinct <= n and 0 <= ascents <= n-1,
            f"endpoint r={r}, n={n}, x={x}: impossible distinct/ascent count")
    return multiplicities + (distinct, ascents)


def validate_histograms(document, counts):
    exact_keys(document, ("schema_version", "coverage", "rows"), "histograms")
    same(integer(document["schema_version"], "histogram schema", 1), 1, "histogram schema")
    coverage = document["coverage"]
    exact_keys(coverage, ("r_min", "r_max", "n_min", "n_max"), "histogram coverage")
    for key, target in {"r_min": 2, "r_max": 6, "n_min": 1, "n_max": N}.items():
        same(integer(coverage[key], f"histogram coverage {key}"), target, f"histogram coverage {key}")
    result = {}
    for row in array(document["rows"], "histogram rows"):
        exact_keys(row, ("r", "n", "endpoints"), "histogram row")
        r = integer(row["r"], "histogram r", 2, 6)
        n = integer(row["n"], "histogram n", 1, N)
        require((r, n) not in result, f"duplicate histogram row r={r}, n={n}")
        hist = {}
        for item in array(row["endpoints"], f"endpoints r={r}, n={n}"):
            exact_keys(item, ("x", "count"), "endpoint")
            x = array(item["x"], "endpoint x")
            same(len(x), r, f"endpoint dimension r={r}, n={n}")
            for j, value in enumerate(x, 1):
                integer(value, f"endpoint X_{j}", 0, n+1)
            x = tuple(x)
            require(sum(x) <= n+1, f"endpoint r={r}, n={n}: too many labels")
            endpoint_statistics(r, n, x)
            require(x not in hist, f"duplicate endpoint r={r}, n={n}, x={x}")
            hist[x] = integer(item["count"], "endpoint count", 1)
        require(bool(hist), f"empty endpoint list r={r}, n={n}")
        same(sum(hist.values()), counts[r][n], f"endpoint total r={r}, n={n}")
        result[r, n] = hist
    same(set(result), {(r, n) for r in RS for n in range(1, N+1)},
         "histogram (r,n) coverage")
    return result


PUBLISHED_SPECS = {
    "A202058": ("https://oeis.org/A202058", {2}, 11),
    "A294220": ("https://oeis.org/A294220", set(RS), 8),
}


def validate_published(document):
    exact_keys(document, ("schema_version", "retrieved", "sources"), "published")
    same(integer(document["schema_version"], "published schema", 1), 1, "published schema")
    same(document["retrieved"], "2026-10-02", "published retrieval date")
    result = {}
    seen = set()
    for source in array(document["sources"], "published sources"):
        exact_keys(source, ("oeis", "url", "n_min", "n_max", "rows"), "published source")
        name = source["oeis"]
        require(type(name) is str and name in PUBLISHED_SPECS, "unknown published source")
        require(name not in seen, f"duplicate published source {name}")
        seen.add(name)
        url, rs, maximum = PUBLISHED_SPECS[name]
        same(source["url"], url, f"published URL {name}")
        same(integer(source["n_min"], "published n_min"), 0, f"published n_min {name}")
        same(integer(source["n_max"], "published n_max"), maximum, f"published n_max {name}")
        source_rs = set()
        for row in array(source["rows"], f"published rows {name}"):
            exact_keys(row, ("r", "values"), "published row")
            r = integer(row["r"], "published r", 2, 6)
            require(r in rs and r not in source_rs, f"invalid/duplicate published r={r} in {name}")
            source_rs.add(r)
            values = array(row["values"], f"published values {name}, r={r}")
            same(len(values), maximum+1, f"published n coverage {name}, r={r}")
            for n, value in enumerate(values):
                integer(value, f"published {name} r={r}, n={n}", 1)
            result[name, r] = values
        same(source_rs, rs, f"published r coverage {name}")
    same(seen, set(PUBLISHED_SPECS), "published source coverage")
    return result


def literal(r, maximum):
    """Enumerate actual words, using only their definition (no capacity transition)."""
    totals = [1] + [0] * maximum
    histograms = [None] + [defaultdict(int) for _ in range(maximum)]
    statistics = [None] + [defaultdict(int) for _ in range(maximum)]
    usages = [0] * (maximum + 2)
    usages[0] = 1

    def visit(n, last, ascents, distinct):
        totals[n] += 1
        x = tuple(sum(value == r-j for value in usages) for j in range(1, r))
        x += (ascents + 2 - distinct,)
        histograms[n][x] += 1
        multiplicities = tuple(sum(value == k for value in usages) for k in range(1, r+1))
        statistics[n][multiplicities + (distinct, ascents)] += 1
        if n == maximum:
            return
        for value in range(ascents + 2):
            used = usages[value]
            if used < r:
                usages[value] += 1
                visit(n+1, value, ascents + int(value > last), distinct + int(used == 0))
                usages[value] -= 1

    if maximum:
        visit(1, 0, 0, 1)
    return totals, histograms, statistics


def unsorted(r, maximum):
    """Ordered residual labels. Exhausted labels alone are removed; never sorted."""
    current = {((r-1, r), 1): 1}
    totals = [1]
    histograms = [None]
    for n in range(1, maximum+1):
        histogram = defaultdict(int)
        for (capacities, threshold), count in current.items():
            x = tuple(capacities.count(j) for j in range(1, r+1))
            histogram[x] += count
        totals.append(sum(current.values()))
        histograms.append(dict(histogram))
        if n == maximum:
            break
        following = defaultdict(int)
        for (capacities, threshold), count in current.items():
            for i, capacity in enumerate(capacities):
                changed = list(capacities)
                changed[i] -= 1
                if capacity == 1:
                    del changed[i]
                if i >= threshold:
                    changed.append(r)
                following[(tuple(changed), i+int(capacity > 1))] += count
        current = following
    return totals, histograms


def compact(r, maximum):
    """Sorted category-count transfer, implemented independently of unsorted()."""
    initial = tuple(int(j in (r-1, r)) for j in range(1, r+1))
    current = {(initial, 1): 1}
    totals = [1]
    histograms = [None]
    for n in range(1, maximum+1):
        histogram = defaultdict(int)
        for (x, threshold), count in current.items():
            histogram[x] += count
        totals.append(sum(current.values()))
        histograms.append(dict(histogram))
        if n == maximum:
            break
        following = defaultdict(int)
        for (x, threshold), count in current.items():
            left = 0
            for j, size in enumerate(x):
                for i in range(left, left+size):
                    changed = list(x)
                    changed[j] -= 1
                    if j:
                        changed[j-1] += 1
                    if i >= threshold:
                        changed[-1] += 1
                    following[(tuple(changed), i+int(j > 0))] += count
                left += size
        current = following
    return totals, histograms


def verify_enumeration(expected_counts, expected_histograms, published):
    endpoint_records = 0
    literal_words = 0
    for r in RS:
        maximum = N+1 if r == 2 else N
        lt, lh, ls = literal(r, maximum)
        ut, uh = unsorted(r, maximum)
        ct, ch = compact(r, maximum)
        same(lt, ut, f"literal/unsorted totals r={r}")
        same(lt, ct, f"literal/compact totals r={r}")
        same(lt[:N+1], expected_counts[r], f"frozen counts r={r}")
        for n in range(1, maximum+1):
            same(dict(lh[n]), uh[n], f"literal/unsorted full X histogram r={r}, n={n}")
            same(dict(lh[n]), ch[n], f"literal/compact full X histogram r={r}, n={n}")
            if n <= N:
                same(dict(lh[n]), expected_histograms[r, n], f"frozen full X histogram r={r}, n={n}")
                endpoint_records += len(lh[n])
            recovered = defaultdict(int)
            for x, count in ch[n].items():
                recovered[endpoint_statistics(r, n, x)] += count
            same(dict(recovered), dict(ls[n]), f"full original-statistics histogram r={r}, n={n}")
            if n < maximum:
                same(sum(sum(x)*count for x, count in ch[n].items()), ct[n+1],
                     f"exact extension identity r={r}, n={n}")
        for (name, published_r), values in published.items():
            if published_r == r:
                same(lt[:len(values)], values, f"published {name} overlap r={r}")
        literal_words += sum(lt[1:])
        print(f"PASS r={r}: three exact models and complete X/statistics histograms through n={maximum}; c[{N},{r}]={ct[N]}", flush=True)
    return endpoint_records, literal_words


@lru_cache(maxsize=None)
def refined_suffix(r, capacities, threshold, length):
    """Immutable full distribution of (final capacity histogram, new ascents)."""
    if length == 0:
        return ((tuple(capacities.count(j) for j in range(1, r+1)), 0, 1),)
    result = defaultdict(int)
    for i, capacity in enumerate(capacities):
        changed = list(capacities)
        changed[i] -= 1
        if capacity == 1:
            del changed[i]
        ascent = int(i >= threshold)
        if ascent:
            changed.append(r)
        for x, a, count in refined_suffix(r, tuple(changed), i+int(capacity > 1), length-1):
            result[x, a+ascent] += count
    return tuple((x, a, count) for (x, a), count in sorted(result.items()))


def verify_adjacent_swaps():
    tested = 0
    for r in range(2, 5):
        for size in range(2, 5):
            for capacities in product(range(1, r+1), repeat=size):
                for threshold in range(2, size+1):
                    for i in range(threshold-1):
                        swapped = list(capacities)
                        swapped[i], swapped[i+1] = swapped[i+1], swapped[i]
                        for length in range(5):
                            same(refined_suffix(r, capacities, threshold, length),
                                 refined_suffix(r, tuple(swapped), threshold, length),
                                 f"adjacent swap r={r}, capacities={capacities}, L={threshold}, i={i}, length={length}")
                            tested += 1
        refined_suffix.cache_clear()
    same(tested, 12220, "adjacent-swap test coverage")
    print(f"PASS {tested} adjacent-swap equalities of complete (X, new ascents) distributions", flush=True)
    return tested


def eulerian_row(size):
    row = [1]
    for n in range(1, size+1):
        row = [(k+1)*(row[k] if k < len(row) else 0) +
               (n-k)*(row[k-1] if k else 0) for k in range(n)]
    return row


def check_buffered_path(r, b, x, q, selected, threshold, positive=False):
    boundaries = [0]
    for value in x:
        boundaries.append(boundaries[-1]+value)
    current = list(x)
    used_categories = [0]*r
    ascents = 0
    expected_ascents = 1 + sum(selected[k] < selected[k+1] for k in range(1, b-2))
    for label in selected:
        category = next((j for j in range(r) if sum(current[:j]) <= label < sum(current[:j+1])), None)
        require(category is not None, f"buffered label {label} is unavailable")
        original = next((j for j in range(r) if boundaries[j] <= label < boundaries[j+1]), None)
        same(category, original, "buffered label retains its category")
        used_categories[category] += 1
        ascent = int(label >= threshold)
        ascents += ascent
        current[category] -= 1
        if category:
            current[category-1] += 1
        current[-1] += ascent
        threshold = label+int(category > 0)
    same(used_categories, q, "buffered category usages")
    expected = [x[j]+q[j+1]-q[j] for j in range(r-1)] + [x[-1]+expected_ascents-q[-1]]
    same(current, expected, "buffered endpoint drift")
    same(ascents, expected_ascents, "buffered permutation ascent formula")
    require(0 <= threshold <= current[0], "buffered final threshold closure")
    if positive:
        require(all(after > before for after, before in zip(current, x)), "strictly positive block drift")
    return expected_ascents-1


def select_buffered_labels(x, q, b, shift=0):
    selected = []
    left = 0
    for size, number in zip(x, q):
        start = left+b+shift
        require(start+number <= left+size-b, "safe-label set too small")
        selected.extend(range(start, start+number))
        left += size
    same(len(selected), b, "buffered selected-label count")
    same(len(set(selected)), b, "buffered labels distinct")
    return selected


def verify_buffered_blocks():
    tested = 0
    for r in RS:
        for b in range(3, 9):
            for case in range(6):
                x = [4*b+3+((case+2)*(j+1) % b) for j in range(r)]
                q = [0]*r
                q[0] = q[-1] = 1
                for t in range(b-2):
                    q[(t+case) % r] += 1
                selected = select_buffered_labels(x, q, b, case % 3)
                low, high = min(selected), max(selected)
                middle = [label for label in selected if label not in (low, high)]
                observed = [0]*(b-2)
                for order in permutations(middle):
                    path = [high]+list(order)+[low]
                    for threshold in (0, x[0]//2, x[0]):
                        k = check_buffered_path(r, b, x, q, path, threshold)
                        observed[k] += 1
                        tested += 1
                same(observed, [3*value for value in eulerian_row(b-2)], "complete middle-permutation Eulerian counts")
    same(tested, 78570, "buffered permutation test coverage")
    positive = 0
    for r in RS:
        q = list(range(3, r+3))
        b = sum(q)
        x = [4*b+j for j in range(r)]
        selected = select_buffered_labels(x, q, b)
        path = [max(selected)] + sorted(selected[1:-1]) + [min(selected)]
        check_buffered_path(r, b, x, q, path, x[0], positive=True)
        positive += 1
    same(positive, 5, "strictly positive block coverage")
    print(f"PASS {tested} deterministic buffered paths, all middle permutations, and {positive} strictly positive-drift blocks", flush=True)
    return tested, positive


def run(data_directory, validate_only=False, enumeration_only=False):
    counts = validate_counts(load_json(data_directory / "expected_counts.json"))
    histograms = validate_histograms(load_json(data_directory / "expected_histograms.json"), counts)
    published = validate_published(load_json(data_directory / "published_counts.json"))
    print("PASS strict reference schemas and required coverage", flush=True)
    if validate_only:
        return
    endpoint_records, words = verify_enumeration(counts, histograms, published)
    print(f"PASS {endpoint_records} frozen endpoint bins; {words} literal nonempty prefix visits", flush=True)
    if not enumeration_only:
        verify_adjacent_swaps()
        verify_buffered_blocks()
    print("PASS all requested exact checks (finite corroboration, not an asymptotic proof)", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data-dir", type=Path, default=DATA)
    parser.add_argument("--validate-only", action="store_true")
    parser.add_argument("--enumeration-only", action="store_true")
    args = parser.parse_args()
    try:
        run(args.data_dir, args.validate_only, args.enumeration_only)
    except VerificationError as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
