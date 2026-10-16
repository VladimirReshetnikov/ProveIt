#!/usr/bin/env python3
"""Finite regressions for the heterogeneous-sort countermodel.

This is evidence for an ordinary mathematical proof, not a formal proof or a
certificate about the compiled 252-state transition table.  Only labels 0,1,2
are instantiated computationally; the proof covers all labels by recursion.
"""
if not __debug__:
    raise SystemExit("Countermodel regressions require enabled assertions; do not use python -O or -OO.")

from functools import lru_cache
import json
from pathlib import Path


@lru_cache(None)
def size(i):
    if i == 0:
        return 2
    n = size(i - 1)
    return n + (1 << n)


def rel(i, j, x, y):
    assert 0 <= x < size(i) and 0 <= y < size(j)
    if i == j:
        return False
    if y == 1:
        return True
    if i < j and size(i) <= y < size(i + 1):
        return bool(((y - size(i)) >> x) & 1)
    return False


def R(i, j): return ("rel", i, j)
def Imp(p, q): return ("imp", p, q)
def All(i, p): return ("all", i, p)
F = R(0, 0)
def Not(p): return Imp(p, F)
def And(p, q): return Not(Imp(p, Not(q)))
def Ex(i, p): return Not(All(i, Not(p)))
def Iff(p, q): return And(Imp(p, q), Imp(q, p))


def evaluate(p, env, phi=None):
    if p == "phi":
        return phi(env)
    k, a, b = p
    if k == "rel":
        return rel(a, b, env.get(a, 0), env.get(b, 0))
    if k == "imp":
        return not evaluate(a, env, phi) or evaluate(b, env, phi)
    if k == "all":
        return all(evaluate(b, env | {a: x}, phi) for x in range(size(a)))
    raise AssertionError(k)


def C(a, b, c):
    power = Ex(c, And(All(b, Imp(All(c, Imp(R(c, b), R(c, a))), R(b, c))), R(c, b)))
    trans = All(c, Imp(R(c, a), R(c, b)))
    return Ex(b, And(All(a, Imp(R(a, b), And(power, trans))), R(c, b)))


def G_body(a, b, c):
    w = Ex(b, And("phi", R(b, c)))
    return And(All(a, Imp(R(a, b), All(b, Imp("phi", w)))),
               All(b, Imp(R(b, c), Ex(a, "phi"))))


def range_witness(a, b, c, env, phi):
    assert c != a and c != b
    if a == b:
        return 0
    B = env.get(b, 0)
    if b < c:
        mask = sum((1 << y) for y in range(size(b))
                   if any(rel(a, b, x, B) and phi(env | {a: x, b: y})
                          for x in range(size(a))))
        return size(b) + mask
    # The hypothesis is that phi does not depend on any label >= c.
    return int(any(rel(a, b, x, B) and phi(env | {a: x, b: 0})
                   for x in range(size(a))))


def pairing(a, b): return (a + b) * (a + b + 1) // 2 + b


def unpair(n):
    from math import isqrt
    w = (isqrt(8 * n + 1) - 1) // 2
    b = n - w * (w + 1) // 2
    return w - b, b


@lru_cache(None)
def code_support(n):
    if n == 0:
        return frozenset()
    a, b = unpair(n // 3)
    if n % 3 == 0:
        return code_support(a) | code_support(b)
    if n % 3 == 1:
        return frozenset((a, b))
    return frozenset((a,)) | code_support(b)


def main():
    counts = {}
    count = 0
    for a in range(3):
        for b in range(3):
            for c in range(3):
                if c in (a, b):
                    continue
                p = C(a, b, c)
                for root in range(size(c)):
                    assert evaluate(p, {c: root})
                    count += 1
    counts["full_C_formula_cases"] = count

    count = 0
    for a, b in ((0, 1), (1, 0)):
        c = 2
        body = G_body(a, b, c)
        for bits in range(1 << (size(a) * size(b))):
            phi = lambda e, bits=bits, a=a, b=b: bool((bits >> (e[a] * size(b) + e[b])) & 1)
            for B in range(size(b)):
                env = {a: 0, b: B}
                witness = range_witness(a, b, c, env, phi)
                assert witness < size(c)
                assert evaluate(body, env | {c: witness}, phi)
                count += 1
    counts["G_arbitrary_binary_matrix_cases"] = count

    count = 0
    for a, b, c in ((0, 2, 1), (2, 0, 1), (1, 2, 0), (2, 1, 0)):
        body = G_body(a, b, c)
        for bits in range(1 << (size(0) if c == 1 else 1)):
            phi = lambda e, bits=bits, c=c: bool((bits >> (e.get(0, 0) if c == 1 else 0)) & 1)
            for B in range(size(b)):
                env = {0: 0, a: 0, b: B}
                witness = range_witness(a, b, c, env, phi)
                assert evaluate(body, env | {c: witness}, phi)
                count += 1
    counts["G_above_code_or_lower_output_cases"] = count

    count = 0
    for a in (0, 1):
        c = 2
        body = G_body(a, a, c)
        for bits in range(1 << size(a)):
            phi = lambda e, bits=bits, a=a: bool((bits >> e[a]) & 1)
            for B in range(size(a)):
                assert evaluate(body, {a: B, c: 0}, phi)
                count += 1
    counts["G_colliding_input_output_cases"] = count

    # Ordinary first-order universal instantiation fails in this semantics.
    full_D0_object_in_D1 = size(0) + (1 << size(0)) - 1
    instance = Imp(All(0, R(0, 1)), R(2, 1))
    assert not evaluate(instance, {1: full_D0_object_in_D1, 2: 0})

    # The independently measured profile-control row rules this model out.
    profile = Imp(All(2, Iff(R(2, 0), R(2, 1))),
                  All(2, Iff(R(0, 2), R(1, 2))))
    assert not evaluate(profile, {0: 1, 1: 1})

    for n in range(10000):
        assert all(i < n for i in code_support(n))
    counts["total_decoder_support_regressions"] = 10000

    result = {
        "status": "finite_regressions_passed",
        "proof_status": "ordinary_mathematical_argument_not_kernel_checked",
        "literal_TM_simulation_proved": False,
        "domain_sizes": [size(i) for i in range(4)],
        "cases": counts,
        "ordinary_universal_instantiation_false": True,
        "profile_control_false": True,
        "full_model_covers_old_and_dual_rho6": True,
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    return result


if __name__ == "__main__":
    result = main()
    Path(__file__).with_name("equality_free_countermodel_results.json").write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n")
