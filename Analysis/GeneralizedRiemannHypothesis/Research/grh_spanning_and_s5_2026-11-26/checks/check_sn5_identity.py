#!/usr/bin/env python3
"""Check the S5 identity in exact rational arithmetic, using only the standard library.

No numerical optimizer or character-table database is used. We generate the
three small subgroups directly, verify their cyclic-character homomorphisms,
compute individual character values in explicit cyclotomic rings, check
their Galois averages through Ramanujan sums, and verify
the identity on every conjugacy class of all 120 permutations of S5.
"""
from collections import Counter, deque
from fractions import Fraction as Q
from itertools import permutations
from math import factorial, gcd
from pathlib import Path
import json


def mul(p, q):
    return tuple(p[q[i]] for i in range(len(p)))


def from_cycles(n, cycles):
    p = list(range(n))
    used = set()
    for cycle in cycles:
        c = [j - 1 for j in cycle]
        assert c and len(set(c)) == len(c)
        assert all(0 <= j < n and j not in used for j in c)
        used.update(c)
        for a, b in zip(c, c[1:] + c[:1]):
            p[a] = b
    return tuple(p)


def cycle_type(p):
    seen, lengths = set(), []
    for i in range(len(p)):
        if i in seen:
            continue
        j, length = i, 0
        while j not in seen:
            seen.add(j)
            length += 1
            j = p[j]
        if length > 1:
            lengths.append(length)
    return tuple(sorted(lengths))


def sign_type(t):
    return (-1) ** sum(k - 1 for k in t)


def mobius(n):
    value, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            value = -value
            if n % p == 0:
                return 0
        p += 1
    return -value if n > 1 else value


def phi(n):
    return sum(gcd(j, n) == 1 for j in range(1, n + 1))


def averaged_root(d, k):
    """(1/phi(d)) sum_{u in (Z/d)^*} exp(2*pi*i*u*k/d)."""
    common = gcd(d, k)
    return Q(sum(a * mobius(d // a) for a in range(1, common + 1)
                 if common % a == 0), phi(d))


def root_pair(d, k):
    """Exact zeta_d^k in Z + Z*zeta_d for d=2,4,6."""
    k %= d
    if d == 2:
        return ((-1) ** k, 0)
    assert d in (4, 6)
    a, b = 1, 0
    for _ in range(k):
        # zeta_4^2=-1, zeta_6^2=zeta_6-1.
        a, b = -b, a + (b if d == 6 else 0)
    return a, b


def subgroup_and_character(n, row):
    d = row["modulus"]
    gens = [(from_cycles(n, g["cycles"]), g["image"] % d)
            for g in row["generators"]]
    identity = tuple(range(n))
    values, queue = {identity: 0}, deque([identity])
    while queue:
        a = queue.popleft()
        for g, image in gens:
            b, exponent = mul(g, a), (image + values[a]) % d
            if b in values:
                assert values[b] == exponent, "inconsistent character images"
            else:
                values[b] = exponent
                queue.append(b)
    assert len(values) == row["expected_order"]
    # Check multiplication and character additivity for every subgroup pair.
    for a, ea in values.items():
        for b, eb in values.items():
            assert values[mul(a, b)] == (ea + eb) % d
    assert set(values.values()) == set(range(d)), "character is not surjective"
    return values


def main():
    cert = json.loads(Path(__file__).with_name("sn5_certificate.json").read_text())
    n = cert["degree"]
    assert n == 5
    types = [tuple(t) for t in cert["class_order"]]
    sizes = Counter(cycle_type(p) for p in permutations(range(n)))
    assert set(types) == set(sizes) and sum(sizes.values()) == factorial(n)
    rows = []
    twist_rows = []
    for row in cert["rows"]:
        elements = subgroup_and_character(n, row)
        aggregate = {t: Q(0) for t in types}
        individual = {t: [0, 0] for t in types}
        twist = {t: Q(0) for t in types}
        for p, e in elements.items():
            t = cycle_type(p)
            value = averaged_root(row["modulus"], e)
            aggregate[t] += value
            aa, bb = root_pair(row["modulus"], e)
            individual[t][0] += aa
            individual[t][1] += bb
            twist[t] += sign_type(t) * value
        assert all(individual[t] == [aggregate[t], 0] for t in types), "individual induction must equal its average"
        actual = [aggregate[t] for t in types]
        assert actual == list(map(Q, row["averaged_row"]))
        rows.append(actual)
        twist_rows.append([twist[t] for t in types])

    target = []
    for t in types:
        fixed = n - sum(t)
        value = -Q(sizes[t] * (fixed - 1), factorial(n))
        if not t:
            value += Q(1, 2)
        if t == (2,):
            value -= Q(1, 2)
        target.append(value)
    assert target == list(map(Q, cert["functional_target"]))
    weights = [Q(r["functional_weight"]) for r in cert["rows"]]
    assert all(w > 0 for w in weights)
    rhs = [sum(weights[j] * rows[j][i] for j in range(len(rows)))
           for i in range(len(types))]
    assert rhs == target

    # Direct induced-character normalization. At g of class t,
    # Ind_H^G(eta)(g) = (|G| / (|H|*|class(t)|)) sum_{h in H cap class(t)} eta(h).
    orders = [r["expected_order"] for r in cert["rows"]]
    induced_weights = [weights[j] * orders[j] for j in range(len(rows))]
    assert induced_weights == [Q(1), Q(1), Q(1)]
    target_character = []
    twisted_values = []
    for i, t in enumerate(types):
        standard = n - sum(t) - 1
        ind_c2_sign = Q(factorial(n), 2 * sizes[t]) * (
            1 if not t else -1 if t == (2,) else 0)
        ind_c2_trivial = Q(factorial(n), 2 * sizes[t]) * (
            1 if not t or t == (2,) else 0)
        value = ind_c2_sign - standard
        direct_rhs = sum(induced_weights[j] * Q(factorial(n), orders[j] * sizes[t])
                         * rows[j][i] for j in range(len(rows)))
        assert value == direct_rhs
        # Four-zeta character: Reg_G + 1 - Ind_C2(1) - Ind_S4(1).
        regular = factorial(n) if not t else 0
        natural_permutation = n - sum(t)
        assert value == regular + 1 - ind_c2_trivial - natural_permutation
        target_character.append(str(value))
        twisted_value = ind_c2_trivial - sign_type(t) * standard
        twisted_rhs = sum(induced_weights[j]
                         * Q(factorial(n), orders[j] * sizes[t])
                         * twist_rows[j][i] for j in range(len(rows)))
        assert twisted_value == twisted_rhs
        twisted_values.append(str(twisted_value))

    # The twists have the arithmetic types claimed in the report.
    c6 = subgroup_and_character(n, cert["rows"][0])
    primitive_twisted_exponents = {(e + (0 if sign_type(cycle_type(p)) == 1 else 3)) % 6
                                  for p, e in c6.items()}
    assert primitive_twisted_exponents == {0, 2, 4}, "twisted C6 character should have order 3"
    v4 = subgroup_and_character(n, cert["rows"][1])
    assert all(sign_type(cycle_type(p)) * ((-1) ** e) == 1 for p, e in v4.items())
    f20 = subgroup_and_character(n, cert["rows"][2])
    assert all((e + (0 if sign_type(cycle_type(p)) == 1 else 2)) % 4 == (-e) % 4
               for p, e in f20.items()), "sign twists quartic character to its conjugate"

    print(json.dumps({
        "status": "PASS: exact rational identities verified on all S5 classes",
        "group_order": factorial(n),
        "class_order": cert["class_order"],
        "class_sizes": [sizes[t] for t in types],
        "subgroup_orders": orders,
        "functional_target": [str(v) for v in target],
        "V5_character_values": target_character,
        "sign_twisted_character_values": twisted_values,
        "positive_induced_weights": [str(v) for v in induced_weights],
        "checks": ["subgroup closure", "character homomorphisms", "individual cyclotomic rows", "Galois trace rows",
                   "functional identity", "induced character identity", "four-zeta character identity", "sign twist identity",
                   "order-three/trivial/quartic sign-twisted Hecke factor types"]
    }, indent=2))


if __name__ == "__main__":
    main()
