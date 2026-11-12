#!/usr/bin/env python3
"""Numerical sanity checks for the scalar-UR predecessor construction.

These checks evaluate the finite scalar descriptions in the standard natural
numbers.  They are not a proof-assistant verification or a check of nonstandard
models.  The complete mathematical proof is in ur_complete.tex and its
included predecessor, reflection, and retraction fragments.
"""
import json
from functools import lru_cache


def iterate(n, a, h):
    for _ in range(n):
        a = h(a)
    return a


def selector(n, a, b):
    # Exactly the value of I(n,a;u.b) in the standard natural numbers.
    return a if n == 0 else b


def unary_iterator(a, h):
    # Memoize initial segments without changing the defining computation.
    values = [a]

    def result(n):
        while len(values) <= n:
            values.append(h(values[-1]))
        return values[n]

    return result


Z = lambda n: selector(n, 1, 0)
N = unary_iterator(0, Z)
j = lambda u: Z(u) + 2 * N(u)
M = unary_iterator(0, j)
g = lambda u: u + N(M(u)) + 1
old_g = lambda u: u + M(u) + 1
G = unary_iterator(0, g)
old_G = unary_iterator(0, old_g)
H = lambda u: selector(N(u), G(u), u)
E = lambda x: iterate(x, 1, lambda u: 2 * u)
L = lambda x, y: N(iterate(y, E(x), H))
B = lambda m, u: selector(L(u + 1, m), u, u + 1)
W = lambda t, m: iterate(t, 0, lambda u: B(m, u))
@lru_cache(None)
def P(m):
    return iterate(m, 0,
                   lambda u: selector(L(u + 2, m), u, u + 1))


@lru_cache(None)
def d(a, b):
    return iterate(b, a, P)


sg = lambda x: selector(x, 0, 1)
bor = lambda x, y: selector(x, y, 1)
mu = lambda n, a: d(n, d(n, a))
phi = lambda n, a, b: mu(n, a) + mu(d(n, a), d(b, a))
m = lambda a, b: a + d(b, a)
delta = lambda a, b: sg(d(a, b) + d(b, a))


def main():
    checks = {}

    def check(name, conditions):
        results = list(conditions)
        assert all(results), name
        checks[name] = len(results)

    check("finite_clock_ranges", (N(n) in (0, 1) and M(n) in (0, 1, 2)
                                  for n in range(101)))
    check("global_modified_ramp_fusion", (M(g(u)) == Z(M(u))
                                          for u in range(101)))
    check("ramp_fusion_consequence", (M(G(n)) == N(n)
                                      for n in range(101)))
    check("same_intended_ramp", (G(n) == old_G(n) for n in range(101)))
    check("ramp_scaling", (G(2 * n) == 3 * n and
                           G(3 * n) == 3 * G(n) + N(n)
                           for n in range(51)))
    check("common_update_for_triple_scaling", (
        G(3 * (n + 1)) == G(3 * n) + M(G(3 * n)) + 4 and
        3 * G(n + 1) + N(n + 1) ==
        3 * G(n) + N(n) + M(3 * G(n) + N(n)) + 4
        for n in range(51)))
    check("factor_map", (H(2 * u) == 3 * u and H(3 * u) == 3 * H(u)
                         for u in range(101)))
    check("comparator_recursions", (
        L(0, y) == 1 and L(x + 1, 0) == 0 and
        L(x + 1, y + 1) == L(x, y)
        for x in range(7) for y in range(7)))
    check("saturated_shift", (W(t + 1, m + 1) == W(t, m) + 1
                               for t in range(6) for m in range(6)))
    check("saturated_diagonal", (L(n + 1, n) == 0 and
                                  W(n, n) == n and W(n + 1, n) == n
                                  for n in range(7)))
    check("predecessor", (P(n + 1) == n for n in range(7)))
    assert P(0) == 0
    check("strict_complement_using_scalar_predecessor", (
        Z(d(n + 1, a)) == sg(d(a, n))
        for n in range(7) for a in range(7)))
    check("comparison_join_using_scalar_predecessor", (
        Z(d(d(x, a), d(b, a))) == bor(Z(d(x, a)), Z(d(x, b)))
        for x in range(7) for a in range(7) for b in range(7)))
    check("explicit_scalar_accumulator_recurrence", (
        phi(n + 1, a, b) == phi(n, a, b) + sg(d(a, n) + d(b, n))
        for n in range(7) for a in range(7) for b in range(7)))
    check("maximum_reduction", (
        m(a, b) == m(P(a), P(b)) + sg(a + b)
        for a in range(7) for b in range(7)))
    check("maximum_common_accumulator", (
        m(d(a, n), d(b, n)) + phi(n, a, b) == m(a, b) and
        m(d(b, n), d(a, n)) + phi(n, a, b) == m(b, a)
        for n in range(7) for a in range(7) for b in range(7)))
    check("actual_equality_characteristic", (
        (delta(a, b) == 0) == (a == b)
        for a in range(7) for b in range(7)))
    # The old update's global fusion law genuinely fails off its orbit.
    old_failure = {"u": 2, "M_old_g_u": M(old_g(2)),
                   "Z_M_u": Z(M(2))}
    assert old_failure["M_old_g_u"] != old_failure["Z_M_u"]
    print(json.dumps({
        "status": "passed",
        "scope": "standard-model numerical sanity checks only",
        "not_claimed_by_these_numerical_checks": [
            "proof-assistant verification",
            "validity in all models",
            "verification of arbitrary proofs"],
        "checks": checks,
        "total_checks": sum(checks.values()) + 2,
        "old_global_fusion_counterexample": old_failure,
        "predecessor_values": [P(n) for n in range(8)]
    }, indent=2))


if __name__ == "__main__":
    main()
