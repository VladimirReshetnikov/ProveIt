#!/usr/bin/env python3
"""Executable word/cut/counting constructions; stdlib only.

All tests below are finite regression checks, not formal iPRA proofs.
"""
from itertools import product, permutations
from math import comb
from pathlib import Path
import json
import random


def encode(q, word):
    result = 0
    for a in word:
        assert 0 <= a < q
        result = (q + 1) * result + a + 1
    return result


def decode(q, code):
    if q == 0:
        return () if code == 0 else None
    out = []
    while code:
        code, last = divmod(code, q + 1)
        if last == 0:
            return None
        out.append(last - 1)
    return tuple(reversed(out))


def star_cuts(predicate, word):
    n = len(word)
    if n == 0:
        return []
    for mask in range(1 << (n - 1)):
        points = [0] + [i for i in range(1, n) if mask & (1 << (i - 1))] + [n]
        factors = [word[i:j] for i, j in zip(points, points[1:])]
        if all(predicate(v) for v in factors):
            return factors
    return None


def star_dp(predicate, word):
    reachable = [True] + [False] * len(word)
    for j in range(1, len(word) + 1):
        reachable[j] = any(reachable[i] and predicate(word[i:j]) for i in range(j))
    return reachable[-1]


def common_power(u, v):
    """Returns a certified decomposition when u v = v u; otherwise None."""
    if u + v != v + u:
        return None
    stack = []
    original_size = len(u) + len(v)
    for _ in range(original_size + 1):
        if not u:
            t, r, s = v, 0, 1
            break
        if not v:
            t, r, s = u, 1, 0
            break
        if len(u) <= len(v):
            assert v[:len(u)] == u
            stack.append("left")
            v = v[len(u):]
        else:
            assert u[:len(v)] == v
            stack.append("right")
            u = u[len(v):]
    else:
        raise AssertionError("descent exceeded the claimed fuel")
    for direction in reversed(stack):
        if direction == "left":
            s = r + s
        else:
            r = r + s
    return t, r, s


def dyck(word):
    height = 0
    for a in word:
        height += 1 if a == 0 else -1
        if height < 0:
            return False
    return height == 0


def reflection(word, target):
    height = 0
    for i, a in enumerate(word):
        height += 1 if a == 0 else -1
        if height == target:
            return tuple(1 - b for b in word[:i + 1]) + word[i + 1:]
    raise ValueError("required first crossing not found")


def poly_add(a, b):
    out = [0] * max(len(a), len(b))
    for i, x in enumerate(a):
        out[i] += x
    for i, x in enumerate(b):
        out[i] += x
    return out


def poly_mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def denominator(matrix):
    r = len(matrix)
    result = [0] * (r + 1)
    for p in permutations(range(r)):
        inversions = sum(p[i] > p[j] for i in range(r) for j in range(i + 1, r))
        term = [(-1) ** inversions]
        for i, j in enumerate(p):
            term = poly_mul(term, [int(i == j), -matrix[i][j]])
        result = poly_add(result, term)
    assert result[0] == 1
    return result


def run_checks():
    codec_checks = cut_checks = commute_checks = reflection_checks = 0
    for q in (1, 2, 3):
        for n in range(6):
            for w in product(range(q), repeat=n):
                c = encode(q, w)
                assert decode(q, c) == w and c < (q + 1) ** n
                codec_checks += 1
                for i in range(n + 1):
                    u, v = w[:i], w[i:]
                    assert c == (q + 1) ** len(v) * encode(q, u) + encode(q, v)
                    cut_checks += 1
    binary = [w for n in range(6) for w in product((0, 1), repeat=n)]
    for u in binary:
        for v in binary:
            witness = common_power(u, v)
            assert (witness is not None) == (u + v == v + u)
            if witness is not None:
                t, r, s = witness
                assert t * r == u and t * s == v
            commute_checks += 1
    star_checks = 0
    for seed in range(20):
        rng = random.Random(seed)
        selected = {w for w in binary if rng.randrange(2)}
        for w in binary:
            factors = star_cuts(selected.__contains__, w)
            assert (factors is not None) == star_dp(selected.__contains__, w)
            if factors is not None:
                assert sum(factors, ()) == w
                assert all(v in selected and v for v in factors)
            star_checks += 1
    catalan = []
    for n in range(8):
        good = 0
        for w in product((0, 1), repeat=2 * n):
            if sum(w) != n:
                continue
            if dyck(w):
                good += 1
            else:
                image = reflection(w, -1)
                assert sum(image) == n - 1
                assert reflection(image, 1) == w
                reflection_checks += 1
        catalan.append(good)
        assert (n + 1) * good == comb(2 * n, n)
        if n:
            assert good == sum(catalan[i] * catalan[n - 1 - i] for i in range(n))
    matrix_checks = recurrence_checks = 0
    for seed in range(32):
        rng = random.Random(seed)
        r = 1 + seed % 4
        delta = [[rng.randrange(r) for _ in range(2)] for _ in range(r)]
        final = [rng.randrange(2) for _ in range(r)]
        matrix = [[sum(delta[i][a] == j for a in range(2)) for j in range(r)]
                  for i in range(r)]
        d = denominator(matrix)
        v = [1] + [0] * (r - 1)
        counts = []
        for n in range(15):
            counts.append(sum(x * y for x, y in zip(v, final)))
            if n <= 7:
                brute = 0
                for w in product((0, 1), repeat=n):
                    state = 0
                    for a in w:
                        state = delta[state][a]
                    brute += final[state]
                assert brute == counts[n]
                matrix_checks += 1
            if n >= r:
                assert sum(d[i] * counts[n - i] for i in range(r + 1)) == 0
                recurrence_checks += 1
            v = [sum(v[i] * matrix[i][j] for i in range(r)) for j in range(r)]
    return {
        "status": "passed", "word_codec_checks": codec_checks,
        "concatenation_cut_checks": cut_checks, "common_power_checks": commute_checks,
        "star_oracle_comparisons": star_checks, "catalan_counts_n_0_to_7": catalan,
        "reflection_inverse_checks": reflection_checks,
        "matrix_vs_word_enumeration_checks": matrix_checks,
        "integer_recurrence_checks": recurrence_checks,
        "foundational_status": "finite executable checks; not a formal proof",
    }


if __name__ == "__main__":
    report = run_checks()
    destination = Path(__file__).resolve().parents[1] / "qa" / "word_count_checks.json"
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
