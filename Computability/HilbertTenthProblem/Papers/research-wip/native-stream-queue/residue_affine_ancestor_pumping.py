#!/usr/bin/env python3
"""Paid scalar residue-affine graphs and exact affine-loader ancestor pumping."""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from itertools import product
import json
from math import gcd, lcm
from pathlib import Path


class Circuit:
    def __init__(self):
        self.counts = Counter()

    def add(self, x, y):
        self.counts['A'] += 1
        return x + y

    def sub(self, x, y):
        self.counts['A'] += 1
        return x - y

    def mul(self, x, y):
        self.counts['M'] += 1
        return x * y


def interpolate(values):
    """Rational coefficient vector for values at 1,...,b; constants only."""
    coefficients = [Fraction(0)] * len(values)
    for i, value in enumerate(values, 1):
        basis, denominator = [Fraction(1)], 1
        for j in range(1, len(values) + 1):
            if i == j:
                continue
            result = [Fraction(0)] * (len(basis) + 1)
            for k, coefficient in enumerate(basis):
                result[k] -= j * coefficient
                result[k + 1] += coefficient
            basis = result
            denominator *= i - j
        for k, coefficient in enumerate(basis):
            coefficients[k] += value * coefficient / denominator
    return coefficients


def table_polynomials(slopes, offsets):
    first = interpolate(slopes)
    second = interpolate([d-a for a, d in zip(slopes, offsets)])
    denominator = lcm(*(c.denominator for c in first + second))
    return denominator, [int(denominator*c) for c in first], [int(denominator*c) for c in second]


def horner(circuit, coefficients, x):
    result = coefficients[-1]
    for coefficient in reversed(coefficients[:-1]):
        result = circuit.add(circuit.mul(result, x), coefficient)
    return result


def scalar_source(circuit, slopes, offsets, n, y, q, s, one_polynomial=False):
    b = len(slopes)
    L, P, G = table_polynomials(slopes, offsets)
    in_left = circuit.add(n, b+1)
    in_right = circuit.add(circuit.mul(b, q), s)
    pv, gv = horner(circuit, P, s), horner(circuit, G, s)
    factors = [circuit.sub(s, i) for i in range(1, b+1)]
    guard = factors[0]
    for factor in factors[1:]:
        guard = circuit.mul(guard, factor)
    out_left = circuit.mul(L, y)
    out_right = circuit.add(circuit.mul(pv, q), gv)
    if one_polynomial:
        r1 = circuit.sub(in_left, in_right)
        r2 = circuit.sub(out_left, out_right)
        return circuit.add(circuit.add(circuit.mul(r1, r1), circuit.mul(r2, r2)), circuit.mul(guard, guard))
    return in_left-in_right, out_left-out_right, guard


def step(n, slopes, offsets):
    q, r = divmod(n, len(slopes))
    return slopes[r]*q + offsets[r]


def run(n, slopes, offsets, length):
    result = [n]
    for _ in range(length):
        result.append(step(result[-1], slopes, offsets))
    return result


def itinerary_affine(states, slopes, offsets):
    """Return A,C with b^t*n_t=A*n_0+C for this exact itinerary."""
    b, A, C, power = len(slopes), 1, 0, 1
    for n in states[:-1]:
        r = n % b
        a, c = slopes[r], b*offsets[r]-slopes[r]*r
        A, C = a*A, a*C+c*power
        power *= b
    assert power*states[-1] == A*states[0]+C
    return A, C


def coprime_part(number, b):
    while gcd(number, b) > 1:
        number //= gcd(number, b)
    return number


def order(base, modulus):
    if modulus == 1:
        return 1
    assert gcd(base, modulus) == 1
    value, exponent = base % modulus, 1
    while value != 1:
        value = value*base % modulus
        exponent += 1
    return exponent


def pump(states, slopes, offsets, loader, shift, k):
    b, t, target = len(slopes), len(states)-1, states[-1]
    A, C = itinerary_affine(states, slopes, offsets)
    perpendicular = coprime_part(loader, b)
    parallel = loader // perpendicular
    assert (b**t*target) % parallel == 0
    period = order(b, A*perpendicular)
    ratio = b**period
    numerator = b**t * ratio**k * target - C
    assert numerator % A == 0
    n = numerator // A
    assert (n-shift) % loader == 0
    return (n-shift)//loader, n, period


def check():
    counts = Counter()
    tables = []
    for b in (2, 3, 4, 6):
        # Positive maps with the exact pure-division residue and unit slopes.
        slopes = tuple(1 if r == 0 else b+1 for r in range(b))
        offsets = tuple(0 if r == 0 else 1+(r % 2) for r in range(b))
        tables.append((slopes, offsets))
        for n in range(1, 81):
            y, q, s = step(n, slopes, offsets), n//b+1, n%b+1
            for one in (False, True):
                circuit = Circuit()
                result = scalar_source(circuit, slopes, offsets, n, y, q, s, one)
                assert result == (0 if one else (0, 0, 0))
                assert circuit.counts == {'M':3*b+3*one, 'A':3*b+1+4*one}
                counts['generated_scalar_graph_checks'] += 1
            # Exhaust independently supplied quotient/selector/output errors.
            for qq, ss, yy in product(range(max(1,q-1),q+2), range(1,b+3), (max(1,y-1),y,y+1)):
                circuit = Circuit()
                result = scalar_source(circuit, slopes, offsets, n, yy, qq, ss, True)
                assert (result == 0) == (qq == q and ss == s and yy == y)
                counts['arbitrary_scalar_graph_checks'] += 1

        for n in range(1, 16):
            for length in range(4):
                states = run(n, slopes, offsets, length)
                A, C = itinerary_affine(states, slopes, offsets)
                for loader in (1, 2, 3, 4, 6, 8, 12):
                    shift = n-loader  # ordinary input x0=1; positive for all x>=1
                    parallel = loader//coprime_part(loader, b)
                    if b**length*states[-1] % parallel:
                        continue
                    previous = 0
                    progression = []
                    for k in range(3):
                        x, initial, period = pump(states, slopes, offsets, loader, shift, k)
                        lifted = run(initial, slopes, offsets, length)
                        assert [v%b for v in lifted[:-1]] == [v%b for v in states[:-1]]
                        assert lifted[-1] == b**(k*period)*states[-1]
                        tail = run(lifted[-1], slopes, offsets, k*period)
                        assert tail[-1] == states[-1]
                        assert x > previous and initial == loader*x+shift
                        previous = x
                        progression.append(x)
                        counts['pumped_exact_histories'] += 1
                    ratio = b**period
                    assert progression[2]-ratio*progression[1] == progression[1]-ratio*progression[0]
                    counts['affine_geometric_progressions'] += 1

        # Independently verify itinerary-to-residue injectivity, including
        # composite b. This justifies the sharpened finite-language bound.
        for length in range(1, 5):
            signatures = {}
            for residue in range(b**length):
                states = run(residue, slopes, offsets, length)
                signature = tuple(v%b for v in states[:-1])
                assert signature not in signatures
                signatures[signature] = residue
            assert len(signatures) == b**length
            counts['itinerary_residue_bijections'] += 1

        # Build preimages directly by solving each branch, independently of
        # forward itinerary enumeration, and check each finite-depth bound.
        for target in range(1, 26):
            ancestors = {target}
            for length in range(5):
                for loader in range(1, 13):
                    for shift in (0, loader-1):
                        covered = {n for n in ancestors
                                   if n > shift and (n-shift) % loader == 0}
                        assert len(covered) <= b**length // gcd(loader, b**length)
                        counts['finite_depth_loader_bounds'] += 1
                predecessors = set()
                for y in ancestors:
                    for r, (a, d) in enumerate(zip(slopes, offsets)):
                        numerator = y-d
                        if numerator >= 0 and numerator % a == 0:
                            n = b*(numerator//a)+r
                            if n > 0:
                                assert step(n, slopes, offsets) == y
                                predecessors.add(n)
                ancestors = predecessors

    # Known finite exception from the older odd-loader result; all other odd
    # starts immediately enter multiples of three and can never reach five.
    slopes, offsets = (1,3), (0,3)
    assert step(5, slopes, offsets) == 9
    assert all(step(n, slopes, offsets) % 3 == 0 for n in range(1,100,2))
    assert all(step(n, slopes, offsets) % 3 == 0 for n in range(3,100,3))

    return {
        'status':'pass',
        'scalar_three_equation_schedule':'3b M + (3b+1) A = 6b+1',
        'scalar_single_polynomial_schedule':'(3b+3) M + (3b+5) A = 6b+8',
        'affine_input_bridge':'1M+1A in the generic case',
        'tests':dict(counts),
        'scope':'Exact scalar graph; ancestor pumping for unit slopes and a pure-division residue, with arbitrary positive affine loader and point target. No decision procedure for arbitrary trajectories or complete certificate below75.'
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write-receipt', action='store_true')
    args = parser.parse_args()
    receipt = check()
    path = Path(__file__).with_suffix('.json')
    if args.write_receipt:
        path.write_text(json.dumps(receipt, indent=2)+'\n')
    else:
        assert json.loads(path.read_text()) == receipt, 'receipt mismatch'
    print(json.dumps(receipt, indent=2))
