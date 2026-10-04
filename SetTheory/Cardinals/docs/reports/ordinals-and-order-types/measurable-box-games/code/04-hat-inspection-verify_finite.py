#!/usr/bin/env python3
"""Exhaustive finite checks for the hat inspection article.

Run with standard Python 3.8 or later:
    python3 code/verify_finite.py

The program uses exact integers only.  It checks the finite blocks and
finite-field constructions; it does not certify the general mathematical
theorems or search over all strategies.  verification.json is written only
after every check succeeds.
"""

import json
from collections import Counter
from pathlib import Path


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def bit(x, coordinate):
    return (x >> coordinate) & 1


def popcount(x):
    # int.bit_count is unavailable in Python 3.8 and 3.9.
    return bin(x).count("1")


def block_prediction(t, player, hats):
    """Adjacent pairs (S,D); return prediction and actual inspected path."""
    if player % 2:
        mate = player - 1
        return 1 - bit(hats, mate), (mate,)
    mate = player + 1
    path = [mate]
    if bit(hats, mate):
        return 1, tuple(path)
    for other in range(t):
        if other in (player, mate):
            continue
        path.append(other)
        if bit(hats, other):
            return 0, tuple(path)
    return 1, tuple(path)


def verify_block(t):
    configurations = 1 << t
    score_histogram = Counter()
    query_histograms = [Counter() for _ in range(t)]
    blind_comparisons = 0
    nonnegative_pair_prefixes = 0
    nonnegative_pair_increments = 0
    for hats in range(configurations):
        correct = []
        for player in range(t):
            prediction, path = block_prediction(t, player, hats)
            require(player not in path, ("own query", t, hats, player))
            require(len(path) == len(set(path)), ("repeated query", t))
            flipped = block_prediction(t, player, hats ^ (1 << player))
            require((prediction, path) == flipped,
                    ("blindness", t, hats, player))
            blind_comparisons += 1
            query_histograms[player][len(path)] += 1
            correct.append(int(prediction == bit(hats, player)))
        excess = sum(correct) - t // 2
        expected = 0
        if hats == 0:
            expected = -t // 2
        elif popcount(hats) == 1:
            white_position = hats.bit_length() - 1
            if white_position % 2 == 0:
                expected = 1
        require(excess == expected, ("block score", t, hats, excess))
        score_histogram[excess] += 1
        if hats:
            for pairs in range(1, t // 2 + 1):
                pair_increment = correct[2 * pairs - 2] + correct[2 * pairs - 1] - 1
                require(pair_increment >= 0,
                        ("negative pair increment", t, hats, pairs))
                nonnegative_pair_increments += 1
                prefix_excess = sum(correct[:2 * pairs]) - pairs
                require(prefix_excess >= 0,
                        ("negative pair prefix", t, hats, pairs))
                nonnegative_pair_prefixes += 1
    expected_scores = Counter({-t // 2: 1, 0: configurations - t // 2 - 1,
                               1: t // 2})
    require(score_histogram == expected_scores, ("score counts", t))
    expected_s_queries = Counter()
    for length in range(1, t - 1):
        expected_s_queries[length] = 1 << (t - length)
    expected_s_queries[t - 1] = 4
    for player in range(t):
        expected_queries = (Counter({1: configurations}) if player % 2
                            else expected_s_queries)
        require(query_histograms[player] == expected_queries,
                ("query law", t, player))
        if player % 2 == 0:
            for r in range(t - 1):
                tail = sum(count for q, count in query_histograms[player].items()
                           if q > r)
                require(tail == (1 << (t - r)),
                        ("query tail", t, player, r))
    return {
        "t": t,
        "configurations": configurations,
        "score_excess_counts": dict(sorted(score_histogram.items())),
        "S_query_counts_per_player": dict(sorted(query_histograms[0].items())),
        "D_query_counts_per_player": dict(sorted(query_histograms[1].items())),
        "blindness_comparisons": blind_comparisons,
        "nonnegative_pair_prefix_checks": nonnegative_pair_prefixes,
        "nonnegative_pair_increment_checks": nonnegative_pair_increments,
    }


# Binary encodings of x+1, x^2+x+1, x^3+x+1, x^4+x+1.
MODULI = {1: 0b11, 2: 0b111, 3: 0b1011, 4: 0b10011}


def gf_mul(a, b, r):
    result = 0
    high = 1 << r
    modulus = MODULI[r]
    while b:
        if b & 1:
            result ^= a
        b >>= 1
        a <<= 1
        if a & high:
            a ^= modulus
    return result


def gf_pow(a, exponent, r):
    result = 1
    while exponent:
        if exponent & 1:
            result = gf_mul(result, a, r)
        exponent >>= 1
        a = gf_mul(a, a, r)
    return result


def gf_trace(a, r):
    result = 0
    for _ in range(r):
        result ^= a
        a = gf_mul(a, a, r)
    require(result in (0, 1), ("trace outside F2", r, result))
    return result


def verify_trace(r, m=1):
    q = 1 << r
    n = m * (q - 1)
    s = m * (q // 2)
    k = s - 1
    configurations = 1 << n
    for a in range(1, q):
        require(gf_pow(a, q - 1, r) == 1, ("field unit", r, a))
    c = next(a for a in range(1, q) if gf_trace(a, r) == 1)
    labels = [(v, copy) for v in range(1, q) for copy in range(m)]
    weights = [gf_mul(c, gf_pow(v, q - 2, r), r) for v, _ in labels]
    query_masks = []
    for player, (v, _) in enumerate(labels):
        mask = 0
        for other, weight in enumerate(weights):
            coefficient = gf_trace(gf_mul(v, weight, r), r)
            if other == player:
                require(coefficient == 1, ("own coefficient", r, m, player))
            elif coefficient:
                mask |= 1 << other
        require(popcount(mask) == k, ("query depth", r, m, player))
        require(not (mask & (1 << player)), ("own query", r, m, player))
        query_masks.append(mask)
    indegrees = [sum(bool(mask & (1 << i)) for mask in query_masks)
                 for i in range(n)]
    require(indegrees == [k] * n, ("query indegrees", r, m))

    def guess(player, hats):
        return 1 ^ (popcount(hats & query_masks[player]) & 1)

    score_histogram = Counter()
    syndrome_histogram = Counter()
    bad = set()
    blindness_comparisons = 0
    for hats in range(configurations):
        syndrome = 0
        for player, weight in enumerate(weights):
            if bit(hats, player):
                syndrome ^= weight
        score = 0
        for player, (v, _) in enumerate(labels):
            prediction = guess(player, hats)
            require(prediction == guess(player, hats ^ (1 << player)),
                    ("blindness", r, m, hats, player))
            blindness_comparisons += 1
            correct = int(prediction == bit(hats, player))
            require(correct == gf_trace(gf_mul(v, syndrome, r), r),
                    ("trace correctness", r, m, hats, player))
            score += correct
        require(score == (0 if syndrome == 0 else s),
                ("trace score", r, m, hats, score))
        score_histogram[score] += 1
        syndrome_histogram[syndrome] += 1
        if score == 0:
            bad.add(hats)
    expected_bad = 1 << (n - r)
    require(len(bad) == expected_bad, ("bad count", r, m))
    require(score_histogram == Counter({0: expected_bad,
                                        s: configurations - expected_bad}),
            ("score histogram", r, m))
    require(set(syndrome_histogram) == set(range(q)), ("syndrome rank", r, m))
    require(set(syndrome_histogram.values()) == {expected_bad},
            ("uniform syndrome", r, m))
    bad_neighbor_counts = Counter()
    local_change_counts = Counter()
    for hats in range(configurations):
        neighbors = sum((hats ^ (1 << i)) in bad for i in range(n))
        require(neighbors == (0 if hats in bad else m),
                ("failure neighbor count", r, m, hats, neighbors))
        bad_neighbor_counts[neighbors] += 1
        if hats in bad:
            for flipped_coordinate in range(n):
                neighbor = hats ^ (1 << flipped_coordinate)
                changed_other_guesses = sum(
                    guess(j, hats) != guess(j, neighbor)
                    for j in range(n) if j != flipped_coordinate)
                require(changed_other_guesses == k,
                        ("local lower bound", r, m, hats, flipped_coordinate))
                local_change_counts[changed_other_guesses] += 1
    return {
        "r": r,
        "m": m,
        "n": n,
        "s": s,
        "queries_per_player": k,
        "configurations": configurations,
        "score_counts": dict(sorted(score_histogram.items())),
        "syndrome_counts": dict(sorted(syndrome_histogram.items())),
        "failure_neighbor_counts": dict(sorted(bad_neighbor_counts.items())),
        "query_indegree_counts": dict(sorted(Counter(indegrees).items())),
        "boundary_other_guess_change_counts": dict(sorted(local_change_counts.items())),
        "blindness_comparisons": blindness_comparisons,
    }


def main():
    data = {
        "blocks": [verify_block(t) for t in range(2, 13, 2)],
        "trace": [verify_trace(r) for r in range(1, 5)],
        "replicated_trace": [verify_trace(r, m) for r, m in
                              ([(1, m) for m in range(2, 7)]
                               + [(2, m) for m in range(2, 5)]
                               + [(3, 2)])],
    }
    destination = Path(__file__).resolve().parents[1] / "data" / "verification.json"
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n",
                           encoding="utf-8")
    cases = sum(len(value) for value in data.values())
    assignments = sum(row["configurations"]
                      for group in data.values() for row in group)
    print("Passed {} exhaustive cases, {} hat assignments.".format(cases, assignments))
    print("Wrote {}".format(destination))


if __name__ == "__main__":
    main()
