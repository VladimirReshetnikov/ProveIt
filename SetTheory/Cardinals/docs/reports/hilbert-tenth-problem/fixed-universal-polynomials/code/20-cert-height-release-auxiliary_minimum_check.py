#!/usr/bin/env python3
"""Independent, bounded corroboration of AUX_MINIMUM.md.

No imports or execution from upstream sources; no complete tuples generated.
All arithmetic recurrences and tests are authored locally for this check.
"""
from math import isqrt
import json


def need(ok, message):
    if not ok:
        raise ValueError(message)


def pell(S, m):
    x, y = 1, 0
    d = S * S - 1
    for _ in range(m):
        x, y = S * x + d * y, x + S * y
    return x, y


def run():
    counts = {}
    count = 0
    for c in range(8, 257, 8):
        for R in range(3, 2 * c, 4):
            admissible = []
            for m in range(1, c, 2):
                v_residue = (-1) ** ((m - 1) // 2) * m
                positive = (v_residue + R) % c == 0
                need(positive == (m % c in {R % c, (-R) % c}), "auxiliary check line 28")
                need((-v_residue + R) % c != 0, "auxiliary check line 29")
                if positive:
                    admissible.append(m)
            r = R % c
            need(min(admissible) == min(r, c - r), "auxiliary check line 33")
            if 2 * R < c:
                need(min(admissible) == R, "auxiliary check line 35")
            count += 1
    counts['actual_even_c_index_and_sign_cases'] = count

    count = 0
    for S in range(2, 41):
        for m in range(1, 31):
            x, y = pell(S, m)
            need(x * x - (S * S - 1) * y * y == 1, "auxiliary check line 43")
            need((x % S == 0) == (m % 2 == 1), "auxiliary check line 44")
            if m % 2 == 0:
                need(x % S == ((-1) ** (m // 2)) % S, "auxiliary check line 46")
            count += 1
    counts['pell_norm_and_divisibility_cases'] = count

    count = 0
    found = 0
    for S in range(2, 21):
        d = S * S - 1
        expected = set()
        m = 1
        while True:
            x, y = pell(S, m)
            if y > 2000:
                break
            expected.add((x, y))
            m += 1
        actual = set()
        for y in range(1, 2001):
            x = isqrt(d * y * y + 1)
            if x * x == d * y * y + 1:
                actual.add((x, y))
                a, b = x, y
                while b > 1:
                    new_a, new_b = S * a - d * b, S * b - a
                    need(new_a > 0 and 0 < new_b < b, "auxiliary check line 70")
                    need(new_a * new_a - d * new_b * new_b == 1, "auxiliary check line 71")
                    a, b = new_a, new_b
                need((a, b) == (S, 1), "auxiliary check line 73")
                found += 1
            count += 1
        need(actual == expected, "auxiliary check line 76")
    counts['exhaustive_small_pell_candidates'] = count
    counts['small_pell_solutions_classified'] = found

    count = 0
    for A in range(2, 35, 4):
        for p in range(12, 65, 4):
            c = pell(A, p)[1]
            need(c % 8 == 0, "auxiliary check line 84")
            need(c >= (2 * A - 1) ** (p - 1) > 4 * p, "auxiliary check line 85")
            count += 1
    counts['outer_recurrence_and_size_cases'] = count

    count = 0
    for S in range(4, 65, 4):
        for V in range(-8, 9):
            for y in range(0, 17):
                Na = S * S * V * V - (S * S - 1) * y * y
                need(Na % 4 == y * y % 4, "auxiliary check line 94")
                need(Na != -1, "auxiliary check line 95")
                count += 1
    counts['negative_norm_mod4_cases'] = count

    count = 0
    max_bits = 0
    for c in range(8, 49, 8):
        for R in range(3, c // 2, 4):
            for Delta in (3, 7, 15):
                previous = None
                for i in range(1, 5):
                    S = i * Delta * c * c
                    F = Delta * i * i * c ** 4 + 1
                    x, y = pell(S, R)
                    need(x % S == 0, "auxiliary check line 109")
                    V = x // S
                    need((V + R * F) % c == 0, "auxiliary check line 111")
                    U = (V + R * F) // c + 1
                    need(U > 0 and y > 0, "auxiliary check line 113")
                    need(S * S * V * V - (S * S - 1) * y * y == 1, "auxiliary check line 114")
                    if previous is not None:
                        prev_F, prev_V, prev_y, prev_U = previous
                        need(F > prev_F and V > prev_V, "auxiliary check line 117")
                        need(y > prev_y and U > prev_U, "auxiliary check line 118")
                    previous = F, V, y, U
                    max_bits = max(max_bits, x.bit_length(), y.bit_length())
                    count += 1
    counts['variable_i_monotonicity_cases'] = count
    counts['largest_variable_i_test_integer_bits'] = max_bits
    return {
        'status': 'PASS',
        'scope': 'Bounded corroboration only; source read as data; no upstream code or full tuples.',
        'counts': counts,
    }


if __name__ == '__main__':
    print(json.dumps(run(), indent=2, sort_keys=True))
