#!/usr/bin/env python3
"""Finite edge-case checks for the independently proved pooling theorem.

This is not an unbounded proof or a ZFC formalization. It exercises signed
Pell parameters, zero and unit bases, negative indices, mixed signs, and
the singleton/pool restoration formulas with exact integer arithmetic.
"""

from fractions import Fraction
from random import Random
import json


def pell(a, k):
    x, y = 1, 0
    for _ in range(abs(k)):
        x, y = a*x+(a*a-1)*y, x+a*y
    return x, y if k >= 0 else -y


def check_case(a, blocks, expected):
    rationals = []
    unweighted_rationals = []
    original_divisibilities = []
    for n, requests in blocks:
        t = 2*a*n-n*n-1
        if not t:
            raise AssertionError("modulus vanished")
        h = s = 0
        deltas = []
        for m, k in requests:
            if max(n*n, m*m, k*k) >= 258:
                raise AssertionError("square-frame precondition failed")
            x, y = pell(a, k)
            z = a*y
            d = m-x+z
            delta = d-n*y
            h += y*(m-x)
            s += d*d-y*y
            deltas.append((delta, y))
            # Signed-power congruence, avoiding modular inverses at n=0.
            if n:
                mod = abs(t)
                nk = pow(n, k, mod)
                if (x+(n-a)*y-nk) % mod:
                    raise AssertionError("signed Pell congruence failed")
        e = s-2*n*h
        if sum(delta*delta for delta, y in deltas) != e-t*sum(y*y for delta, y in deltas):
            raise AssertionError("pool identity failed")
        rationals.append(Fraction(n*e, t))
        unweighted_rationals.append(Fraction(e, t))
        original_divisibilities.append(e % t == 0)
        if expected:
            if any(delta % t for delta, y in deltas):
                raise AssertionError("singleton quotient failed")
            ell = e//t
            kay = 2*h+(2*a-n)*ell
            if kay-2*h-(2*a-n)*ell or s-n*kay+ell:
                raise AssertionError("pool restoration failed")
            for delta, y in deltas:
                quotient = -delta//t
                if delta+t*quotient:
                    raise AssertionError("singleton restoration failed")
    actual = sum(rationals, Fraction(0)).denominator == 1
    unweighted_actual = sum(unweighted_rationals, Fraction(0)).denominator == 1
    if actual != expected or unweighted_actual != expected or all(original_divisibilities) != expected:
        raise AssertionError("exact reciprocal integrality criterion failed")


def main():
    rng = Random(20261025)
    magnitude = 258**258+1
    count = 0
    for a in (magnitude, -magnitude):
        check_case(a, [(0, [(m, k) for m, k in ((-7, -3), (8, 0), (13, 5))])], True)
        count += 1
        for _ in range(40):
            bases = [0, -1, 1, rng.choice((-4, -3, -2)), rng.choice((2, 3, 4))]
            blocks = []
            for n in bases:
                requests = []
                for _ in range(rng.randint(1, 3)):
                    if n == 0:
                        requests.append((rng.randint(-16, 16), rng.randint(-16, 16)))
                    elif abs(n) == 1:
                        k = rng.randint(-16, 16)
                        requests.append((1 if n == 1 or k % 2 == 0 else -1, k))
                    else:
                        k = rng.randint(0, 2)
                        requests.append((n**k, k))
                blocks.append((n, requests))
            check_case(a, blocks, True)
            count += 1
            # A deliberately false output at a nonzero base.
            bad = [(n, list(requests)) for n, requests in blocks]
            m, k = bad[-1][1][0]
            bad[-1][1][0] = (m-1, k)
            check_case(a, bad, False)
            count += 1
            # A negative index at a nonunit base cannot have an integer power.
            negative = [(n, list(requests)) for n, requests in blocks]
            negative[-1][1][0] = (0, -1)
            check_case(a, negative, False)
            count += 1
        # Repeated bases and hence repeated, noncoprime moduli.
        repeated = [(2, [(4, 2)]), (2, [(2, 1)]), (-1, [(-1, -3)]), (0, [(16, -16)])]
        check_case(a, repeated, True)
        count += 1
        repeated[1][1][0] = (3, 1)
        check_case(a, repeated, False)
        count += 1
    # Literal small-height example printed in the report. Every k=0 pair
    # is (1,0), so E is the sum of (m-1)^2. Both moduli fail divisibility,
    # while their unweighted reciprocal sum is the integer zero.
    control_a=10
    cx,cy=pell(control_a,0)
    if (cx,cy)!=(1,0):
        raise AssertionError("zero-index control pair failed")
    control_t=(2*control_a-2,-2*control_a-2)
    control_e=(sum((m-cx)**2 for m in (4,)),sum((m-cx)**2 for m in (4,2,2)))
    negative_control=sum((Fraction(e,t) for e,t in zip(control_e,control_t)),Fraction(0))
    if control_t!=(18,-22) or control_e!=(9,11) or negative_control!=0 or any(e%t==0 for e,t in zip(control_e,control_t)):
        raise AssertionError("small-height cancellation control failed")
    return {
        "status": "pass",
        "exact_cases": count,
        "W": 258,
        "A": "+/-(258^258+1)",
        "criteria_checked": ["oriented reciprocal integrality", "unweighted reciprocal integrality", "original block divisibilities"],
        "small_height_control": {"A":control_a,"bases":[1,-1],"indices":[0,0,0,0],"moduli":list(control_t),"numerators":list(control_e),"reciprocal_sum":0,"both_divisibilities_fail":True},
        "coverage": ["zero bases", "both unit bases", "mixed base signs", "both signs of A", "signed indices", "true witnesses", "false outputs", "impossible negative nonunit powers", "singleton and pool restoration", "repeated bases and noncoprime moduli", "small-height cancellation negative control"],
        "scope": "Finite arithmetic regression checks; unbounded theorem proved separately."
    }


if __name__ == "__main__":
    print(json.dumps(main(), indent=2))
