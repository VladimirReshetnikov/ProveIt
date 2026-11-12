#!/usr/bin/env python3
"""Bounded sanity checks for the cancellative initial structure.

These tests concern the initial first-order structure only. They neither
construct the nonprincipal ultrapowers nor verify the final infinite model.
The mathematical proof, rather than the finite checks, establishes the laws
for all elements and the extension tower's existence.
"""

import json


ZERO = (0, 0)
ONE = (0, 1)
COUNTEREXAMPLE = (1, 0)


def member(value):
    first, second = value
    return first > 0 or (first == 0 and second >= 0)


def add(left, right):
    return left[0] + right[0], left[1] + right[1]


def successor(value):
    return value[0], value[1] + 1


def predecessor(value):
    if value == ZERO:
        return None
    return value[0], value[1] - 1


def identity_iterator(count, seed):
    return seed if count[0] == 0 else ONE


def successor_iterator(count, seed):
    return add(seed, count)


def su_test_function(value):
    return add(value, identity_iterator(value, ZERO))


def run():
    samples = [(0, n) for n in range(5)]
    samples += [(k, z) for k in (1, 2) for z in range(-3, 4)]
    checks = 0

    def require(claim, label):
        nonlocal checks
        checks += 1
        if not claim:
            raise ValueError(label)

    for a in samples:
        require(member(a), "sample membership")
        require(member(successor(a)), "successor closure")
        require(successor(a) != ZERO, "successor omits zero")
        require(add(a, ZERO) == a, "additive identity")
        require(successor(a) == add(a, ONE), "successor as addition")
        require(identity_iterator(ZERO, a) == a, "identity iterator at zero")
        require(successor_iterator(ZERO, a) == a, "successor iterator at zero")
        require(successor_iterator(a, ZERO) == a, "successor identity orbit")
        require(su_test_function(successor(a)) == successor(su_test_function(a)),
                "SU test function recurrence")
        if a != ZERO:
            p = predecessor(a)
            require(member(p) and successor(p) == a, "coverage")
        for length in range(1, 13):
            require((a[0], a[1] + length) != a, "bounded successor cycle")
        for b in samples:
            require(member(add(a, b)), "addition closure")
            require(add(a, b) == add(b, a), "commutativity")
            require(add(a, successor(b)) == successor(add(a, b)),
                    "addition successor equation")
            require(identity_iterator(successor(a), b) == identity_iterator(a, b),
                    "identity iterator successor computation")
            require(successor_iterator(successor(a), b)
                    == successor(successor_iterator(a, b)),
                    "successor iterator successor computation")
            require(add(a, b) != ZERO or (a == ZERO and b == ZERO), "conicality")
            require(successor(a) != successor(b) or a == b, "successor injectivity")
            for c in samples:
                require(add(add(a, b), c) == add(a, add(b, c)), "associativity")
                require(add(a, b) != add(a, c) or b == c, "cancellation")

    require(identity_iterator(COUNTEREXAMPLE, ZERO) == ONE, "failed induction")
    require(su_test_function(ZERO) == ZERO, "SU test function base")
    require(su_test_function(COUNTEREXAMPLE) != COUNTEREXAMPLE,
            "the structure does not satisfy full successor uniqueness")
    return {
        "scope": "Bounded checks of the initial structure only; not a formal proof "
                 "or a construction of the final ultrapower tower.",
        "domain": "{(0,n): n is nonnegative} union {(k,z): k is positive, z is integer}",
        "sample_elements": len(samples),
        "successful_checks": checks,
        "failures": 0,
        "counterexample_c": COUNTEREXAMPLE,
        "J_c_zero": identity_iterator(COUNTEREXAMPLE, ZERO),
        "successor_orbit_c_zero": successor_iterator(COUNTEREXAMPLE, ZERO),
        "SU_counterexample_f_c": su_test_function(COUNTEREXAMPLE),
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
