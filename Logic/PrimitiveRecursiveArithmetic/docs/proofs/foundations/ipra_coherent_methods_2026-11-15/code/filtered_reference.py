#!/usr/bin/env python3
"""Exact finite diagnostics for the filtered-lifting and Hurwitz theorems.

Standard library only. These checks are not object-iPRA derivations and do
not replace the human proofs. Polynomial coefficients are stored low-degree
first as finite (coefficient, exponent-vector) lists; duplicate terms work.
"""
from fractions import Fraction
from itertools import product
from math import comb, factorial
import json
from pathlib import Path
import sys


class ModRing:
    def __init__(self, q, precision):
        assert q >= 2 and precision >= 1
        self.q, self.N = q, precision
        self.modulus = q ** precision
        self.zero, self.one = 0, 1

    def integer(self, n):
        return n % self.modulus

    def add(self, a, b):
        return (a + b) % self.modulus

    def neg(self, a):
        return (-a) % self.modulus

    def mul(self, a, b):
        return a * b % self.modulus

    def member(self, k, a):
        return a % (self.q ** min(k, self.N)) == 0


class JetRing:
    def __init__(self, precision):
        assert precision >= 1
        self.N = precision
        self.zero = (Fraction(0),) * precision
        self.one = self.integer(1)

    def integer(self, n):
        return (Fraction(n),) + (Fraction(0),) * (self.N - 1)

    def monomial(self, degree, coefficient=1):
        return tuple(Fraction(coefficient) if j == degree else Fraction(0)
                     for j in range(self.N))

    def add(self, a, b):
        return tuple(x + y for x, y in zip(a, b))

    def neg(self, a):
        return tuple(-x for x in a)

    def mul(self, a, b):
        return tuple(sum(a[j] * b[n - j] for j in range(n + 1))
                     for n in range(self.N))

    def member(self, k, a):
        return all(x == 0 for x in a[:min(k, self.N)])


def sum_r(ring, xs):
    s = ring.zero
    for x in xs:
        s = ring.add(s, x)
    return s


def power(ring, x, n):
    s = ring.one
    for _ in range(n):
        s = ring.mul(s, x)
    return s


def evaluate(ring, polynomial, point):
    def term_value(term):
        c, exponents = term
        v = c
        assert len(exponents) == len(point)
        for x, e in zip(point, exponents):
            v = ring.mul(v, power(ring, x, e))
        return v
    return sum_r(ring, map(term_value, polynomial))


def partial(ring, polynomial, j):
    answer = []
    for c, e in polynomial:
        if e[j]:
            f = list(e)
            f[j] -= 1
            answer.append((ring.mul(ring.integer(e[j]), c), tuple(f)))
    return answer


def jacobian(ring, polys, point):
    return [[evaluate(ring, partial(ring, p, j), point)
             for j in range(len(point))] for p in polys]


def mat_vec(ring, matrix, vector):
    return [sum_r(ring, (ring.mul(a, b) for a, b in zip(row, vector)))
            for row in matrix]


def mat_mul(ring, left, right):
    m = len(left)
    return [[sum_r(ring, (ring.mul(left[i][k], right[k][j])
                         for k in range(m)))
             for j in range(m)] for i in range(m)]


def subtract(ring, a, b):
    return ring.add(a, ring.neg(b))


def frozen_lift(ring, polys, seed, inverse):
    """Return the state after N-1 updates, verifying each precision contract."""
    m = len(seed)
    assert len(polys) == m and len(inverse) == m
    assert all(len(row) == m for row in inverse)
    derivative = jacobian(ring, polys, seed)
    for prod in (mat_mul(ring, derivative, inverse),
                 mat_mul(ring, inverse, derivative)):
        for i in range(m):
            for j in range(m):
                target = ring.one if i == j else ring.zero
                assert ring.member(1, subtract(ring, target, prod[i][j]))
    state = list(seed)
    trace = [state]
    for r in range(ring.N):
        residual = [evaluate(ring, p, state) for p in polys]
        assert all(ring.member(r + 1, v) for v in residual)
        assert all(ring.member(1, subtract(ring, x, a))
                   for x, a in zip(state, seed))
        if r + 1 < ring.N:
            correction = mat_vec(ring, inverse, residual)
            assert all(ring.member(r + 1, v) for v in correction)
            state = [subtract(ring, x, v)
                     for x, v in zip(state, correction)]
            trace.append(state)
    assert all(evaluate(ring, p, state) == ring.zero for p in polys)
    return state, trace


def jet_system(n, perturbed=False):
    r = JetRing(n)
    # Y = 1 + (T/2) Z^2; Z = 2 + (T/3) Y.
    p = [(r.one, (1, 0)), (r.integer(-1), (0, 0)),
         (r.monomial(1, Fraction(-1, 2)), (0, 2))]
    q = [(r.one, (0, 1)), (r.integer(-2), (0, 0)),
         (r.monomial(1, Fraction(-1, 3)), (1, 0))]
    a = [r.one, r.integer(2)]
    u = [[r.one, r.zero], [r.zero, r.one]]
    if perturbed:
        a = [r.add(a[0], r.monomial(1, 7)),
             r.add(a[1], r.monomial(1, -3))]
        u = [[r.add(r.one, r.monomial(1, 2)), r.monomial(1, 5)],
             [r.monomial(1, -1), r.add(r.one, r.monomial(1, 4))]]
    return r, [p, q], a, u


def modular_polynomial(ring, coeffs):
    return [(ring.integer(c), (j,)) for j, c in enumerate(coeffs)]


def hurwitz_product(a, b, n):
    return sum(comb(n, j) * a[j] * b[n - j] for j in range(n + 1))


def main():
    result = {"scope": "Exact finite diagnostics; not universal or object-theory proofs."}

    # Two distinct rational jet series, coherence, and independence of lifts.
    r, ps, a, u = jet_system(12)
    jets, _ = frozen_lift(r, ps, a, u)
    for n in range(1, 13):
        low = frozen_lift(*jet_system(n))[0]
        altered = frozen_lift(*jet_system(n, perturbed=True))[0]
        assert low == [j[:n] for j in jets]
        assert altered == low
    result["simultaneous_rational_jets"] = {
        "precision": 12,
        "Y": [str(x) for x in jets[0]],
        "Z": [str(x) for x in jets[1]],
        "coherence_and_independence_precisions_checked": list(range(1, 13))}

    # Explicit scalar lift at a composite base.
    r = ModRing(4, 3)
    p = modular_polynomial(r, [-2, -1, 0, 1])
    scalar, trace = frozen_lift(r, [p], [2], [[3]])
    assert scalar == [22] and trace == [[2], [54], [22]]
    result["composite_scalar"] = {"q": 4, "N": 3, "trace": trace,
                                  "root": scalar[0]}

    # Simultaneous modular system: X + Y^2 = 5; Y + X^2 = 1.
    system_outputs = []
    for n in range(1, 4):
        r = ModRing(4, n)
        ps = [[(r.one, (1, 0)), (r.one, (0, 2)),
               (r.integer(-5), (0, 0))],
              [(r.one, (0, 1)), (r.one, (2, 0)),
               (r.integer(-1), (0, 0))]]
        root, trace = frozen_lift(r, ps, [0, 1], [[1, 2], [0, 1]])
        roots = [[x, y] for x in range(0, r.modulus, 4)
                 for y in range(1, r.modulus, 4)
                 if all(evaluate(r, p, [x, y]) == 0 for p in ps)]
        assert roots == [root]
        if system_outputs:
            assert [x % (4 ** (n-1)) for x in root] == system_outputs[-1]
        system_outputs.append(root)
    result["composite_simultaneous"] = {
        "q": 4, "roots_at_precisions_1_2_3": system_outputs,
        "unique_in_seed_residue_class_by_exhaustive_enumeration": True}

    # Exhaust all quadratic coefficient triples in [-2,2], all simple root
    # residues, q=2,...,7, and N=1,...,3. Inverse discovery is a finite scan.
    instances = 0
    candidate_points = 0
    for q in range(2, 8):
        for cs in product(range(-2, 3), repeat=3):
            for seed in range(q):
                if sum(c * seed ** j for j, c in enumerate(cs)) % q:
                    continue
                d = (cs[1] + 2 * cs[2] * seed) % q
                us = [u for u in range(q) if u * d % q == 1]
                if not us:
                    continue
                previous = None
                for n in range(1, 4):
                    r = ModRing(q, n)
                    p = modular_polynomial(r, cs)
                    root, _ = frozen_lift(r, [p], [seed], [[us[0]]])
                    candidates = range(seed, r.modulus, q)
                    candidate_points += len(candidates)
                    roots = [x for x in candidates if evaluate(r, p, [x]) == 0]
                    assert roots == root
                    if previous is not None:
                        assert root[0] % (q ** (n-1)) == previous
                    previous = root[0]
                    instances += 1
    result["exhaustive_modular"] = {
        "bases": list(range(2, 8)), "precisions": [1, 2, 3],
        "coefficient_range": [-2, 2], "max_degree": 2,
        "lifting_instances": instances,
        "candidate_root_residues_checked": candidate_points}

    # The N-1 bound is sharp: the frozen inverse need not give quadratic gain.
    r = ModRing(4, 5)
    p = modular_polynomial(r, [-4, 1])
    sharp, trace = frozen_lift(r, [p], [0], [[5]])
    assert all(evaluate(r, p, s) != 0 for s in trace[:-1])
    assert sharp == [4]
    result["sharp_iteration_bound"] = {"q": 4, "N": 5, "trace": trace,
                                       "all_earlier_residuals_nonzero": True}

    # Dropping the inverse hypothesis really invalidates uniqueness.
    r = ModRing(2, 2)
    p = modular_polynomial(r, [0, 0, 1])
    assert [x for x in range(0, 4, 2) if evaluate(r, p, [x]) == 0] == [0, 2]
    result["missing_inverse_counterexample"] = {
        "polynomial": "X^2", "modulus": 4, "seed_mod_2": 0, "roots": [0, 2]}

    bell = [1]
    quadratic_ode = [1]
    for n in range(15):
        bell.append(sum(comb(n, j) * bell[n-j] for j in range(n+1)))
        quadratic_ode.append(hurwitz_product(quadratic_ode, quadratic_ode, n))
    assert bell[:11] == [1, 1, 2, 5, 15, 52, 203, 877, 4140, 21147, 115975]
    assert quadratic_ode == [factorial(n) for n in range(16)]
    # A direct finite test of the exact one-coefficient derivative demand.
    a = list(range(1, 18))
    b = [(-1) ** n * (n+2) for n in range(17)]
    for n in range(16):
        assert hurwitz_product(a, b, n+1) == (
            hurwitz_product(a[1:], b, n) + hurwitz_product(a, b[1:], n))
    result["hurwitz"] = {"bell_coefficients_through_15": bell,
                          "Yprime_equals_Y_squared_gives_factorials": True,
                          "leibniz_coefficient_tests": 16}
    result["all_checks_passed"] = True
    payload = json.dumps(result, indent=2) + "\n"
    if len(sys.argv) > 1:
        Path(sys.argv[1]).write_text(payload)
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
