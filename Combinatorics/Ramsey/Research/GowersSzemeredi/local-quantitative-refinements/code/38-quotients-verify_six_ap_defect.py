#!/usr/bin/env python3
"""Exact finite-field checks for the six-term norm-core defect formula.

Standard library only.  The script exhausts all elements of F_(q^5)
for q=7,13 in the quadratic-coefficient check, and all elements of
F_(q^3) in the norm-fiber check.  It independently counts the weighted
core fibers before comparing with the closed character formula.
This is a certificate of the finite examples, not a proof in general.
It does not enumerate all q^20 center--direction pairs in the
ten-dimensional examples.  Run from any working directory; the JSON
report is saved in the project's data/six_ap_defect_checks.json.
"""
from collections import Counter
from fractions import Fraction
from itertools import product
from pathlib import Path
import json


def require(b, message):
    if not b:
        raise ArithmeticError(message)


def remainder(a, b, p):
    a = list(a)
    while len(a) >= len(b):
        c, s = a[-1], len(a) - len(b)
        for j, v in enumerate(b):
            a[j + s] = (a[j + s] - c * v) % p
        while a and a[-1] == 0:
            a.pop()
    return a


def irreducible(f, p):
    return all(remainder(f, list(c) + [1], p)
               for d in range(1, (len(f) - 1) // 2 + 1)
               for c in product(range(p), repeat=d))


def find_modulus(n, p):
    for c in product(range(p), repeat=n):
        if c[0] and irreducible(list(c) + [1], p):
            return list(c) + [1]
    raise ArithmeticError("No irreducible modulus")


class Field:
    def __init__(self, p, f):
        self.p, self.f, self.n = p, f, len(f) - 1
        self.zero = (0,) * self.n
        self.one = (1,) + (0,) * (self.n - 1)

    def add(self, x, y):
        return tuple((a + b) % self.p for a, b in zip(x, y))

    def scale(self, c, x):
        return tuple(c * a % self.p for a in x)

    def mul(self, x, y):
        p, n = self.p, self.n
        z = [0] * (2 * n - 1)
        for i, a in enumerate(x):
            for j, b in enumerate(y):
                z[i + j] += a * b
        for k in range(2 * n - 2, n - 1, -1):
            c = z[k] % p
            for j in range(n):
                z[k - n + j] -= c * self.f[j]
        return tuple(a % p for a in z[:n])

    def power(self, x, e):
        z = self.one
        while e:
            if e & 1:
                z = self.mul(z, x)
            x = self.mul(x, x)
            e //= 2
        return z


def chi(a, q):
    a %= q
    if a == 0:
        return 0
    return 1 if pow(a, (q - 1) // 2, q) == 1 else -1


def e2_coefficients(field):
    """Build e2 directly as the sum of pairwise Frobenius conjugates."""
    q, n = field.p, field.n
    basis = [tuple(int(i == j) for i in range(n)) for j in range(n)]
    conj = [[field.power(e, q ** r) for e in basis] for r in range(n)]
    coeff = []
    for i in range(n):
        for j in range(i, n):
            value = field.zero
            for r in range(n):
                for s in range(r + 1, n):
                    value = field.add(value, field.mul(conj[r][i], conj[s][j]))
                    if i != j:
                        value = field.add(value, field.mul(conj[r][j], conj[s][i]))
            require(not any(value[1:]), "e2 coefficient is not in the base field")
            if value[0]:
                coeff.append((i, j, value[0]))
    return coeff


def check_case(q):
    f5, f3 = find_modulus(5, q), find_modulus(3, q)
    E, K = Field(q, f5), Field(q, f3)
    coeff = e2_coefficients(E)
    distribution = Counter(sum(c * x[i] * x[j] for i, j, c in coeff) % q
                           for x in product(range(q), repeat=5))
    for c in range(q):
        require(distribution[c] == q ** 4 + chi(2 * c, q) * q ** 2,
                f"Wrong e2 count for q={q}, c={c}")

    norm3 = Counter()
    for x in product(range(q), repeat=3):
        v = K.power(x, q ** 2 + q + 1)
        require(not any(v[1:]), "Cubic norm left the base field")
        norm3[v[0]] += 1
    require(norm3[0] == 1, "Cubic norm has a nonzero zero")
    require(all(norm3[c] == q ** 2 + q + 1 for c in range(1, q)),
            "Incorrect nonzero cubic norm fiber")

    L5 = sum(q ** j for j in range(5))
    all_targets, category_values = 0, {}
    # Multiplication by a fixed nonzero quintic direction bijects its
    # centers with x in F_(q^5).  This sum is therefore an independent
    # exact count of cubic choices over all quintic centers.
    for b5 in range(1, q):
        for b3 in range(q):
            direct = L5 * sum(multiplicity * norm3[(b3 - b5 * c) % q]
                             for c, multiplicity in distribution.items())
            symbol = chi(2 * b3 * pow(b5, -1, q), q)
            predicted = L5 * (q ** 7 - (q ** 4 + q ** 3) * symbol)
            require(direct == predicted, "Averaged core fiber mismatch")
            category_values[str(symbol)] = {
                "sum_over_quintic_centers": direct,
                "mean_over_quintic_centers": str(Fraction(direct, q ** 5))}
            all_targets += 1
    for b3 in range(q):
        require(q ** 5 * norm3[b3] == q ** 5 *
                (1 + (q ** 2 + q) * int(b3 != 0)),
                "Zero quintic-target fiber mismatch")

    # Evaluate three different added functions at the actual six nodes.
    # Compute the complete progression count by the fiber lookup, then
    # independently compare with the claimed aggregated defect formula.
    examples = []
    for degree in (3, 4, 5):
        T0 = T1 = S = full_count = 0
        half = pow(2, -1, q)
        for b in range(q):
            for g in range(q):
                vals = [pow((b + (2 * i - 5) * half * g) % q, degree, q)
                        for i in range(6)]
                D3 = (vals[4] - 3 * vals[3] + 3 * vals[2] - vals[1]) % q
                D5 = (vals[5] - 5 * vals[4] + 10 * vals[3] -
                      10 * vals[2] + 5 * vals[1] - vals[0]) % q
                beta5 = D5 * pow(120, -1, q) % q
                beta3 = (D3 * pow(6, -1, q) - D5 * pow(48, -1, q)) % q
                if beta5 == 0:
                    H = q ** 5 * norm3[(-beta3) % q]
                    T0 += int(D3 != 0)
                else:
                    T1 += 1
                    symbol = chi((40 * D3 * pow(D5, -1, q) - 5) % q, q)
                    S += symbol
                    H = L5 * sum(count * norm3[(-beta3 + beta5 * c) % q]
                                  for c, count in distribution.items())
                full_count += q ** 4 * H
        full_count -= q ** 10  # Exactly one zero direction at each center.
        predicted = (q ** 10 * (q - 1) + q ** 9 * (q ** 2 + q) * T0 +
                     q ** 9 * (q ** 2 * L5 - 1) * T1 -
                     q ** 7 * (q + 1) * L5 * S)
        require(full_count == predicted, "Global defect identity mismatch")
        if degree == 5:
            require(T0 == 0 and T1 == q * (q - 1) and
                    S == (q - 1) ** 2 * chi(5, q),
                    "Fifth-power defect statistics mismatch")
        examples.append({"R": f"w^{degree}", "T0": T0, "T1": T1,
                         "S": S, "ordered_nontrivial_symmetric_6APs": full_count})
    return {
        "q": q, "degree5_modulus_ascending": f5,
        "degree3_modulus_ascending": f3,
        "e2_quadratic_coefficients_i_j_value": coeff,
        "degree5_elements_exhausted": q ** 5,
        "e2_value_distribution": dict(sorted(distribution.items())),
        "degree3_norm_elements_exhausted": q ** 3,
        "nonzero_quintic_target_pairs_checked": all_targets,
        "fiber_categories_by_quadratic_character": category_values,
        "R_examples": examples,
    }


if __name__ == "__main__":
    report = {"status": "all exact checks passed",
              "cases": [check_case(7), check_case(13)]}
    path = Path(__file__).resolve().parents[1] / "data" / "six_ap_defect_checks.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
