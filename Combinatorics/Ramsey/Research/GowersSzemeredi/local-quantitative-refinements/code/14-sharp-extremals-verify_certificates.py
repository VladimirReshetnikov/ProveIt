#!/usr/bin/env python3
"""Exact finite certificates for the support and torsion tables.

Only Python's standard library is used.  This supplements, and does
not replace, the general proofs in the article.
"""
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent


def rank(rows):
    a = [[Fraction(v) for v in row] for row in rows]
    if not a:
        return 0
    r = 0
    for col in range(len(a[0])):
        pivot = next((i for i in range(r, len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        q = a[r][col]
        a[r] = [v/q for v in a[r]]
        for i in range(len(a)):
            if i != r and a[i][col]:
                q = a[i][col]
                a[i] = [v-q*w for v, w in zip(a[i], a[r])]
        r += 1
        if r == len(a):
            break
    return r


def determinant(rows):
    if len(rows) == 1:
        return rows[0][0]
    return sum((-1)**i * rows[0][i] *
               determinant([r[:i]+r[i+1:] for r in rows[1:]])
               for i in range(len(rows)))


def support_table():
    vertices = list(product((0, 1), repeat=3))
    forms = [(1,) + v for v in vertices]
    output = []
    for size in range(1, 9):
        surviving = 0
        classes = Counter()
        for subset in combinations(range(8), size):
            rows = [forms[i] for i in subset]
            r = rank(rows)
            coloops = sum(rank(rows[:i]+rows[i+1:]) < r
                          for i in range(size))
            classes[(r, coloops)] += 1
            surviving += coloops == 0
            if size == 5 and coloops == 0:
                missing = [vertices[i] for i in range(8) if i not in subset]
                assert any(all(sum(a != b for a, b in zip(v, c)) == 1
                               for v in missing) for c in vertices)
        output.append({"size": size, "total": sum(classes.values()),
                       "surviving_centered_supports": surviving,
                       "rank_coloop_counts":
                       [{"rank": k[0], "coloops": k[1], "count": v}
                        for k, v in sorted(classes.items())]})
    assert [x["surviving_centered_supports"] for x in output] == [0, 0, 0, 12, 8, 28, 8, 1]
    minors = sorted({determinant([list(forms[i]) for i in sub])
                     for sub in combinations(range(8), 4)})
    assert minors == [-2, -1, 0, 1, 2]
    return {"rows": output, "four_by_four_minors": minors,
            "five_vertex_survivors": "complements of the three neighbors of one vertex"}


def polynomial(*terms):
    """Terms are (coefficient, delta power, rho power, b power)."""
    return {tuple(t[1:]): t[0] for t in terms}


def clean(counter):
    return {k: v for k, v in counter.items() if v}


def square(poly):
    out = Counter()
    for x, a in poly.items():
        for y, b in poly.items():
            out[tuple(v+w for v, w in zip(x, y))] += a*b
    return clean(out)


def torsion_table(n):
    # W's Fourier support: coefficient amplitudes delta, rho, and b.
    # In order five, the phase of a_j is z^j, z=exp(pi*i/10).
    amplitudes = {0: (1, 0, 0), 1: (0, 1, 0), -1: (0, 1, 0),
                  2: (0, 0, 1), -2: (0, 0, 1)}
    data = {j % n: (v, j if n == 5 else 0)
            for j, v in amplitudes.items()}
    common = {
        (0, 0): polynomial((1, 4, 0, 0), (2, 0, 4, 0), (2, 0, 0, 4)),
        (1, 1): polynomial((1, 2, 2, 0), (2, 1, 2, 1)),
        (2, 2): polynomial((1, 2, 0, 2)),
    }
    expected = dict(common)
    if n == 5:
        expected.update({
            (0, 1): polynomial((2, 2, 2, 0), (2, 0, 2, 2), (1, 0, 0, 4)),
            (0, 2): polynomial((2, 2, 0, 2), (2, 0, 2, 2), (1, 0, 4, 0)),
            (1, 2): polynomial((1, 0, 2, 2), (2, 1, 2, 1)),
        })
    else:
        expected.update({
            (0, 1): polynomial((2, 2, 2, 0), (2, 0, 2, 2)),
            (0, 2): polynomial((2, 2, 0, 2), (1, 0, 4, 0)),
            (0, 3): polynomial((1, 0, 0, 4), (2, 0, 2, 2)),
            (1, 2): polynomial((2, 1, 2, 1)),
            (1, 3): polynomial((1, 0, 2, 2)),
            (2, 3): {},
            (3, 3): polynomial((2, 0, 1, 3)),
        })
    multiplicities = Counter()
    Q = Counter()
    for s, t in product(range(n), repeat=2):
        phase_terms = Counter()
        for r in range(n):
            labels = [r, (r+s) % n, (r+t) % n, (r+s+t) % n]
            if any(j not in data for j in labels):
                continue
            powers = tuple(sum(data[j][0][i] for j in labels) for i in range(3))
            phase = sum(sign*data[j][1] for sign, j in
                        zip((1, -1, -1, 1), labels)) % 20
            sign = 1
            if phase >= 10:
                phase -= 10
                sign = -1
            # All phases are 1, -1, i or -i; z^5=i and z^10=-1.
            assert phase in (0, 5)
            phase_terms[(powers, phase)] += sign
        phase_terms = clean(phase_terms)
        assert all(phase == 0 for (powers, phase) in phase_terms)
        actual = {powers: value for (powers, phase), value in phase_terms.items()}
        kind = tuple(sorted((min(s, n-s), min(t, n-t))))
        assert actual == expected[kind], (n, s, t, actual, expected[kind])
        multiplicities[kind] += 1
        Q.update(square(actual))
    norm = {(r, b): value for (d, r, b), value in Q.items() if d == 0}
    expected_norm = {(8, 0): 8, (4, 4): 48, (0, 8): 8}
    if n == 5:
        expected_norm.update({(6, 2): 16, (2, 6): 16})
    else:
        expected_norm[(2, 6)] = 32
    assert norm == expected_norm
    positive_delta = {(d, r, b): value for (d, r, b), value in Q.items() if d > 0}
    expected_Q = polynomial((1, 8, 0, 0), (24, 4, 4, 0), (24, 4, 0, 4),
                            (16, 3, 4, 1), (96, 2, 4, 2))
    if n == 5:
        expected_Q.update(polynomial((48, 2, 2, 4), (32, 1, 4, 3)))
    assert positive_delta == expected_Q
    return {
        "order": n, "slots_checked": n*n, "bases_per_slot": n,
        "symmetry_rows": [{"representative": list(k), "multiplicity": v}
                          for k, v in sorted(multiplicities.items())],
        "Q_monomials": [{"powers_delta_rho_b": list(k), "coefficient": v}
                        for k, v in sorted(Q.items(), reverse=True)],
        "arithmetic": "exact integer polynomial coefficients, exact cancellation of imaginary phases",
    }


def main():
    result = {"status": "PASS", "centered_supports": support_table(),
              "order_five": torsion_table(5), "order_seven": torsion_table(7)}
    path = ROOT / "certificate_results.json"
    path.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({"status": "PASS", "output": path.name,
                      "torsion_slots": 25+49, "support_subsets": 255}))


if __name__ == "__main__":
    main()
