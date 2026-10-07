#!/usr/bin/env python3
"""Report199 exact finite checks. Python standard library only; no floating point.

All checks raise explicit exceptions and therefore remain active under python -O.
This program verifies finite identities, not asymptotic estimates or novelty.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
import hashlib
from itertools import combinations, product
import json
import math
from pathlib import Path
import re
import sys

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(100000)

MOMENT_LIMIT = 500
CUMULANT_LIMIT = 160
OEIS_PREFIX = [1, 1, 15, 1490, 472475, 367254494, 596838469302,
    1812465211795364, 9460229930323620755, 79588323526110945959270,
    1025816228173896271039326050, 19441688693651416990291991566332,
    523762848713992063145153491388390686,
    19495503038639783268900576813041922912172]


class VerificationError(ValueError):
    """A mathematical identity, serialized input, or explicit guard failed."""


def require(condition, message):
    if not condition:
        raise VerificationError(message)


def integer(value, name, low, high):
    require(type(value) is int and low <= value <= high,
            f"{name} must be an integer in [{low}, {high}]")
    return value


def no_duplicate_keys(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"Duplicate JSON key: {key}")
        result[key] = value
    return result


def load_json(path):
    try:
        return json.loads(Path(path).read_text(encoding="utf-8"),
            object_pairs_hook=no_duplicate_keys,
            parse_constant=lambda x: (_ for _ in ()).throw(VerificationError(f"Nonfinite JSON value: {x}")))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise VerificationError(f"Cannot read strict UTF-8 JSON: {Path(path).name}") from exc


def canonical_bytes(value):
    return (json.dumps(value, sort_keys=True, indent=2, ensure_ascii=True,
                       allow_nan=False) + "\n").encode("ascii")


def write_json(path, value):
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    Path(path).write_bytes(canonical_bytes(value))


def exact_moments(limit, weight):
    integer(limit, "moment limit", 0, 2000)
    weights = [0] + [weight(h) for h in range(1, limit + 1)]
    require(all(type(x) is int and x > 0 for x in weights[1:]),
            "Weights must be positive integers")
    v = [1] + [0] * limit
    moments = [1]
    for step in range(1, 2 * limit + 1):
        nxt = [0] * (limit + 1)
        for h in range(step % 2, min(step, limit) + 1, 2):
            nxt[h] = v[h - 1] if h else 0
            if h < limit:
                nxt[h] += weights[h + 1] * v[h + 1]
        v = nxt
        if step % 2 == 0:
            moments.append(v[0])
    return moments


def power_coefficients(m, exponent, degree):
    integer(degree, "power degree", 0, len(m) - 1)
    require(type(exponent) is int, "Power exponent must be an integer")
    require(m[0] == 1 and all(type(x) is int for x in m),
            "Power input must be an integer series with constant coefficient 1")
    result = [1]
    for n in range(1, degree + 1):
        value = sum(((exponent + 1) * j - n) * m[j] * result[n - j]
                    for j in range(1, n + 1))
        q, r = divmod(value, n)
        require(r == 0, f"Nonintegral formal power coefficient: degree {n}")
        result.append(q)
    return result


def cumulants(m, limit):
    integer(limit, "cumulant limit", 0, len(m) - 1)
    a = [1]
    for n in range(1, limit + 1):
        q, r = divmod(power_coefficients(m, 1 - 2 * n, n)[n], 1 - 2 * n)
        require(r == 0 and q > 0, f"Invalid cumulant at index {n}")
        a.append(q)
    return a


def multiply(f, g, degree):
    return [sum(f[k] * g[n - k] for k in range(n + 1))
            for n in range(degree + 1)]


def independent_series_checks(m, a, limit=40):
    # Bottom-up truncated S-fraction, distinct from length/height transfer.
    f = [1] + [0] * limit
    for h in range(limit, 0, -1):
        g = [1] + [0] * limit
        for n in range(1, limit + 1):
            g[n] = h**4 * sum(f[k] * g[n - 1 - k] for k in range(n))
        f = g
    require(f == m[:limit + 1], "Continued fraction and path transfer disagree")
    # Direct first-block inversion M=1+sum a_k z^k M^(2k).
    powers = [[1] + [0] * limit]
    for _ in range(2 * limit):
        powers.append(multiply(powers[-1], f, limit))
    recovered = [1]
    for n in range(1, limit + 1):
        recovered.append(f[n] - sum(recovered[k] * powers[2*k][n-k]
                                   for k in range(1, n)))
    require(recovered == a[:limit + 1], "First-block and Lagrange inversion disagree")
    return {"continued_fraction_through": limit, "first_block_inversion_through": limit}


@lru_cache(None)
def dyck_words(n):
    integer(n, "enumeration semilength", 0, 10)
    result = []
    def visit(u, d, word):
        if d == n:
            result.append(word)
            return
        if u < n:
            visit(u + 1, d, word + (1,))
        if d < u:
            visit(u, d + 1, word + (-1,))
    visit(0, 0, ())
    return tuple(result)


def descent_data(word):
    heights = [0]
    downs = []
    for step in word:
        if step < 0:
            downs.append(heights[-1])
        heights.append(heights[-1] + step)
    return heights, Counter(downs)


def all_matchings(vertices):
    if not vertices:
        yield ()
        return
    for j in range(1, len(vertices)):
        for tail in all_matchings(vertices[1:j] + vertices[j+1:]):
            yield ((vertices[0], vertices[j]),) + tail


def all_partitions(n):
    def visit(i, blocks):
        if i == n:
            yield tuple(tuple(b) for b in blocks)
            return
        for j in range(len(blocks)):
            blocks[j].append(i)
            yield from visit(i+1, blocks)
            blocks[j].pop()
        blocks.append([i])
        yield from visit(i+1, blocks)
        blocks.pop()
    yield from visit(0, [])


def is_noncrossing(blocks):
    for b, c in combinations(blocks, 2):
        for u, v in combinations(b, 2):
            for x, y in combinations(c, 2):
                if u < x < v < y or x < u < y < v:
                    return False
    return True


def matching_checks(m, a):
    records = []
    for n in range(1, 4):
        V = 2*n
        edges = list(combinations(range(V), 2))
        bits = {edge: 1 << i for i, edge in enumerate(edges)}
        partitions = []
        for blocks in all_partitions(V):
            if any(len(b) % 2 for b in blocks) or not is_noncrossing(blocks):
                continue
            allowed = sum(bits[edge] for b in blocks for edge in combinations(b, 2))
            partitions.append((len(blocks), allowed, blocks))
        groups = {}
        for matching in all_matchings(tuple(range(V))):
            openers = tuple(sorted(u for u, _ in matching))
            mask = sum(bits[edge] for edge in matching)
            groups.setdefault(openers, []).append(mask)
        @lru_cache(None)
        def closure(mask):
            candidates = [(count, blocks) for count, allowed, blocks in partitions
                          if mask & ~allowed == 0]
            require(bool(candidates), "No containing noncrossing partition")
            count = max(x[0] for x in candidates)
            least = [blocks for c, blocks in candidates if c == count]
            require(len(least) == 1, "Least noncrossing closure is not unique")
            return least[0]
        total = connected = 0
        distribution = Counter()
        for group in groups.values():
            for four in product(group, repeat=4):
                blocks = closure(four[0] | four[1] | four[2] | four[3])
                total += 1
                connected += len(blocks) == 1
                distribution[len(blocks)] += 1
        require(total == m[n] and connected == a[n], f"Matching count mismatch at n={n}")
        if n == 2:
            crossing = bits[(0, 2)] | bits[(1, 3)]
            require(len(closure(crossing)) == 1,
                    "Crossing two-component matching must have one NC closure block")
        records.append({"n": n, "all_quadruples": total,
            "one_noncrossing_closure_block": connected,
            "closure_block_count_distribution": {str(k): v for k, v in sorted(distribution.items())},
            "even_noncrossing_partitions": len(partitions),
            "distinct_edge_unions": closure.cache_info().currsize})
    return records


LAWS = {
    "quartic": lambda h: h**4,
    "four_gamma": lambda h: h*h*(4*h*h-1),
    "alternating_scaled_four": lambda h: (3 if h % 2 else 4)*h**4,
    "irregular_scaled_sixteen": lambda h: (12+(7*h) % 5)*h**4,
}


def path_and_excursion_checks(limit=9):
    pathwise = 0
    for n in range(1, limit+1):
        require(len(dyck_words(n)) == math.comb(2*n, n)//(n+1), "Catalan count mismatch")
        for word in dyck_words(n):
            heights, counts = descent_data(word)
            edge_heights = [max(heights[j:j+2]) for j in range(len(word))]
            require(math.prod(edge_heights) == math.prod(h**c for h, c in counts.items())**2,
                    "All-edge/down-edge product identity failed")
            valleys = [heights[j+1] for j in range(len(word)-1) if word[j:j+2] == (-1, 1)]
            for h in range(1, n+1):
                require(heights.count(h) == counts[h]+counts[h+1], "Slot identity failed")
                require(edge_heights.count(h) == 2*counts[h], "Crossing identity failed")
                require(abs(counts[h]-1) <= sum(v < h for v in valleys), "Low-valley bound failed")
                starts = [j for j, step in enumerate(word) if step < 0 and heights[j] == h]
                for start in starts[:-1]:
                    end = next(j for j in range(start+1, len(heights)) if heights[j] == h)
                    excursion, deleted = word[start:end], word[:start]+word[end:]
                    require(len(excursion) % 2 == 0 and excursion[0] == -1 and excursion[-1] == 1,
                            "Invalid negative-excursion endpoints")
                    require(all(v < h for v in heights[start+1:end]), "Excursion is not primitive")
                    _, deleted_counts = descent_data(deleted)
                    _, relative_counts = descent_data(excursion)
                    translated = Counter({d+h: c for d, c in relative_counts.items()})
                    require(deleted_counts+translated == counts, "Excursion deletion factorization failed")
                pathwise += 1
    records = []
    for name, weight in LAWS.items():
        Z, W, hit = [], [], []
        for n in range(limit+1):
            z, w, reached = 0, [0]*(limit+3), [0]*(limit+3)
            for word in dyck_words(n):
                heights, counts = descent_data(word)
                wt = math.prod(weight(h)**c for h, c in counts.items())
                z += wt
                for h in range(1, limit+2):
                    w[h] += wt*counts[h]
                    reached[h] += wt*(max(heights) >= h)
            Z.append(z); W.append(w); hit.append(reached)
        @lru_cache(None)
        def excursion_weight(h, k):
            v = [0]*h
            v[h-1] = weight(h)
            for _ in range(2*k-2):
                nxt = [0]*h
                for j, x in enumerate(v):
                    if j+1 < h:
                        nxt[j+1] += x
                    if j:
                        nxt[j-1] += x*weight(j)
                v = nxt
            return v[h-1]
        checked = 0
        for n in range(1, limit+1):
            for h in range(1, n+1):
                rhs = sum(excursion_weight(h, k)*(W[n-k][h]+W[n-k][h+1])
                          for k in range(1, n-h+1))
                require(W[n][h]-hit[n][h] == rhs,
                        f"Negative-excursion identity failed: {name}, n={n}, h={h}")
                checked += 1
        records.append({"law": name, "through_n": limit, "exact_identity_pairs": checked})
    return {"pathwise_n_height_pairs": pathwise,
            "dyck_paths_enumerated": sum(len(dyck_words(n)) for n in range(1, limit+1)),
            "weighted_negative_excursion_identities": records}


def occupation_check(n, name, weight):
    cutoff = n//64
    v = [1]+[0]*n
    markers = [[0]*(n+1) for _ in range(cutoff)]
    weights = [0]+[weight(h) for h in range(1, n+1)]
    for step in range(2*n):
        nxt = [0]*(n+1)
        new_markers = [[0]*(n+1) for _ in range(cutoff)]
        for h in range(step % 2, min(step, n)+1, 2):
            x = v[h]
            if h < n:
                nxt[h+1] += x
                for j in range(cutoff):
                    new_markers[j][h+1] += markers[j][h]
            if h:
                nxt[h-1] += x*weights[h]
                for j in range(cutoff):
                    new_markers[j][h-1] += weights[h]*(markers[j][h]+x*(h == j+1))
        v, markers = nxt, new_markers
    Z = v[0]
    rows = []
    for h in range(1, cutoff+1):
        # Paths whose maximum is below h give Pr(N_h=0).
        confined = [1]+[0]*(h-1)
        for _ in range(2*n):
            nxt = [0]*h
            for j, x in enumerate(confined):
                if j+1 < h:
                    nxt[j+1] += x
                if j:
                    nxt[j-1] += x*weights[j]
            confined = nxt
        absolute_numerator = markers[h-1][0]-Z+2*confined[0]
        require(absolute_numerator >= 0, "Negative absolute occupation moment")
        scaled = F(absolute_numerator*n**4, h**4*Z)
        require(scaled <= 15552, f"Finite occupation bound failed: {name}, n={n}, h={h}")
        rows.append({"h": h, "n4_over_h4_times_mean_absolute_deviation": str(scaled)})
    return {"law": name, "n": n, "exact_bound": "15552", "values": rows}


# Polynomials in n are represented by lists of rational coefficients in ascending degree.
def ptrim(a):
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def padd(a, b):
    r = [F(0)]*max(len(a), len(b))
    for i, x in enumerate(a): r[i] += x
    for i, x in enumerate(b): r[i] += x
    return ptrim(r)


def pscale(a, x):
    return ptrim([v*x for v in a])


def pmul(a, b):
    r = [F(0)]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): r[i+j] += x*y
    return ptrim(r)


def polynomial_checks(m, a, degree=8):
    Q = [[F(1)]]
    for j in range(1, degree+1):
        q = [F(0)]
        for k in range(1, j+1):
            q = padd(q, pscale(pmul([F(k-j), F(-2*k)], Q[j-k]), F(m[k], j)))
        Q.append(q)
    U = [0]+a[1:degree+1]
    powers = [[1]+[0]*degree]
    for _ in range(degree): powers.append(multiply(powers[-1], U, degree))
    for j in range(1, degree+1):
        p = [F(0)]
        for ell in range(1, j+1):
            binomial = [F(1)]
            for k in range(ell-1):
                binomial = pmul(binomial, [F(-2*j+ell-1-k), F(2)])
            binomial = pscale(binomial, F(1, math.factorial(ell-1)))
            term = pscale(pmul([F(0), F(2)], binomial),
                          F((-1)**ell*powers[ell][j], ell))
            p = padd(p, term)
        require(p == Q[j], f"Symbolic cyclic-placement polynomial mismatch at grade {j}")
    expected = [[F(1)], [F(0), F(-2)], [F(0), F(-33), F(2)],
                [F(0), F(-9410, 3), F(66), F(-4, 3)]]
    require(Q[:4] == expected, "Displayed Q_0 through Q_3 mismatch")
    for n in range(20, 45):
        numeric = power_coefficients(m, -2*n, degree)
        for j in range(degree+1):
            require(sum(c*n**i for i, c in enumerate(Q[j])) == numeric[j], "Polynomial evaluation mismatch")
    return {"variable": "n", "coefficient_order": "ascending degree",
        "Q": [[str(c) for c in q] for q in Q],
        "symbolic_cyclic_identity_through_grade": degree,
        "integer_specializations_checked": list(range(20, 45))}


def algebra_checks():
    gamma4 = [F(13,48), F(-1,32), F(119,23040)]
    gamma1x4 = [F(1,3), F(0), F(-1,90)]
    difference = [x-y for x, y in zip(gamma4, gamma1x4)]
    require(difference[0] == F(-1,16), "Stirling correction mismatch")
    require(F(1,48)+F(1,4) == gamma4[0], "Shifted gamma first coefficient mismatch")
    require(F(-1,23040)+F(1,192) == gamma4[2], "Shifted gamma third coefficient mismatch")
    require(F(1,3)-F(1,16) == F(13,48), "Inverse d constant mismatch")
    # Sparse Laurent polynomials in B,D,d; exponents of D may be negative.
    def add(*ps):
        ans = {}
        for p in ps:
            for k, v in p.items(): ans[k] = ans.get(k, F(0))+v
        return {k: v for k, v in ans.items() if v}
    def scale(p, f): return {k: v*f for k, v in p.items() if v*f}
    def mul(p, q):
        ans = {}
        for k, v in p.items():
            for l, w in q.items():
                key = tuple(x+y for x, y in zip(k, l))
                ans[key] = ans.get(key, F(0))+v*w
        return {k: v for k, v in ans.items() if v}
    B, D, d = {(1,0,0): F(1)}, {(0,1,0): F(1)}, {(0,0,1): F(1)}
    delta0 = {(1,-1,0): F(-1)}
    bracket = add(scale(mul(delta0, delta0), 2), scale(delta0, F(3,2)), d)
    delta1_times_t = scale(mul({(0,-1,0): F(1)}, bracket), -1)
    require(not add(mul(D, delta0), B), "Inverse constant-order cancellation failed")
    require(not add(mul(D, delta1_times_t), bracket), "Inverse 1/t cancellation failed")
    eta = F(27,256)
    require(1+2*eta/(1-3*eta) == F(229,175), "Cone summation constant mismatch")
    require(3*eta < F(1,3) and F(432,64**4) < F(1,4), "Cone numerical guard failed")
    for s in range(1, 100):
        require(sum(2**q*math.comb(s-1, q-1) for q in range(1, s+1)) == 2*3**(s-1),
                "Ordered-chain count mismatch")
    return {"stirling": {"order": "n^-1,n^-2,n^-3",
            "log_Gamma_4n_plus_2_after_main_terms": [str(x) for x in gamma4],
            "four_log_Gamma_n_plus_1_after_main_terms": [str(x) for x in gamma1x4],
            "classical_comparison_log_correction": [str(x) for x in difference],
            "raw_moment_second_order_claimed": False},
        "inverse": {"variables": ["B", "D", "d"],
            "delta0": "-B/D", "t_delta1": "-(2*delta0^2+3*delta0/2+d)/D",
            "constant_order_residual": "0", "inverse_t_order_residual": "0",
            "d_as_affine_polynomial_in_pi": ["13/48", "-1/16"]},
        "cone_constants": {"eta": str(eta), "three_eta": str(3*eta),
            "internal_bound": str(F(229,175)), "ordered_chain_cases": 99}}


def validate_values(data):
    require(type(data) is dict and set(data) == {"schema", "moment_limit", "cumulant_limit", "m", "a", "four_gamma"},
            "Unexpected exact-values keys")
    require(data["schema"] == "report199-exact-values-v1", "Unexpected values schema")
    integer(data["moment_limit"], "moment_limit", MOMENT_LIMIT, MOMENT_LIMIT)
    integer(data["cumulant_limit"], "cumulant_limit", CUMULANT_LIMIT, CUMULANT_LIMIT)
    for key, count in (("m", MOMENT_LIMIT+1), ("four_gamma", MOMENT_LIMIT+1), ("a", CUMULANT_LIMIT+1)):
        values = data[key]
        require(type(values) is list and len(values) == count, f"Incorrect {key} array length")
        require(all(type(v) is str and len(v) <= 100000 and re.fullmatch(r"0|[1-9][0-9]*", v)
                    for v in values), f"Noncanonical decimal integer in {key}")
        require(values[0] == "1", f"Incorrect constant coefficient in {key}")
    return data


def generate():
    m = exact_moments(MOMENT_LIMIT, LAWS["quartic"])
    four_gamma = exact_moments(MOMENT_LIMIT, LAWS["four_gamma"])
    a = cumulants(m, CUMULANT_LIMIT)
    require(a[:len(OEIS_PREFIX)] == OEIS_PREFIX, "Displayed OEIS prefix mismatch")
    require(all((x % 2 == 1) == (n == 0 or n & (n-1) == 0) for n, x in enumerate(a)),
            "Power-of-two cumulant parity mismatch")
    require(all(x % 2 for x in m), "Quartic moment parity mismatch")
    require(all(m[n]*m[n] <= m[n-1]*m[n+1] for n in range(1, MOMENT_LIMIT)),
            "Moment log-convexity mismatch")
    require(all(m[n] <= 4*n**4*m[n-1] for n in range(1, MOMENT_LIMIT+1)),
            "Moment ratio upper bound mismatch")
    values = {"schema": "report199-exact-values-v1", "moment_limit": MOMENT_LIMIT,
        "cumulant_limit": CUMULANT_LIMIT, "m": list(map(str, m)), "a": list(map(str, a)),
        "four_gamma": list(map(str, four_gamma))}
    validate_values(values)
    checks = {"schema": "report199-exact-checks-v1", "status": "PASS",
        "scope": "Exact finite checks; asymptotic theorems require the written proofs.",
        "oeis": {"id": "A338634", "displayed_terms_checked": len(OEIS_PREFIX),
                 "indices": [0, len(OEIS_PREFIX)-1], "full_b_file_checked": False},
        "cumulant_parity_through": CUMULANT_LIMIT, "moment_parity_through": MOMENT_LIMIT,
        "moment_log_convexity_through": MOMENT_LIMIT-1,
        "moment_ratio_upper_bound_through": MOMENT_LIMIT,
        "independent_series": independent_series_checks(m, a),
        "matching_quadruples": matching_checks(m, a),
        "path_and_negative_excursion": path_and_excursion_checks(),
        "finite_occupation_checks": [occupation_check(n, name, weight)
             for name, weight in LAWS.items() for n in (64,128,256)],
        "algebra": algebra_checks()}
    polynomials = polynomial_checks(m, a)
    return {"exact_values.json": values, "exact_checks.json": checks,
            "shifted_polynomials.json": polynomials}


def replay(output=None, check_data=None):
    results = generate()
    if output is not None:
        out = Path(output)
        out.mkdir(parents=True, exist_ok=True)
        for name, value in results.items(): write_json(out/name, value)
    if check_data is not None:
        source = Path(check_data)
        for name, value in results.items():
            actual = load_json(source/name)
            if name == "exact_values.json": validate_values(actual)
            require(actual == value, f"Recomputed data mismatch: {name}")
            require((source/name).read_bytes() == canonical_bytes(value), f"Noncanonical JSON bytes: {name}")
    return {"status": "PASS", "raw_moments_through": MOMENT_LIMIT,
            "cumulants_through": CUMULANT_LIMIT,
            "files": {name: hashlib.sha256(canonical_bytes(value)).hexdigest()
                      for name, value in sorted(results.items())}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Write deterministic exact JSON files here")
    parser.add_argument("--check-data", type=Path, help="Recompute and strictly compare these exact JSON files")
    args = parser.parse_args()
    if args.output is None and args.check_data is None:
        parser.error("supply --output and/or --check-data")
    try:
        print(json.dumps(replay(args.output, args.check_data), sort_keys=True, indent=2))
    except (VerificationError, OSError) as exc:
        parser.exit(1, f"Exact verification failed: {exc}\n")


if __name__ == "__main__":
    main()
