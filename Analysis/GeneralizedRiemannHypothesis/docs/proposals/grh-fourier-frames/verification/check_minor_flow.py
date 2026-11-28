#!/usr/bin/env python3
"""Exact checks of the ordered crossing coefficients and uniform constant.

All matrix calculations are rational. The integer parameter h in the derivation
scales the three infinitesimal generators. No matrix exponential is evaluated.
For each example we compute the h^2 coefficient of the determinant in two ways:
by expanding exp(h A1) exp(h A2) exp(h A3) and its principal minor directly,
and by solving the crossing-block equation for the degree-two logarithm.
A separate suite uses square-zero generators, for which the exact exponentials
are linear, and rational enclosures for the logarithm of the actual determinant.
"""
from fractions import Fraction as F
from itertools import permutations
from random import Random

def zero(n):
    return [[F(0) for _ in range(n)] for _ in range(n)]

def eye(n):
    return [[F(i == j) for j in range(n)] for i in range(n)]

def add(a, b):
    return [[x + y for x, y in zip(row_a, row_b)] for row_a, row_b in zip(a, b)]

def scale(a, k):
    return [[k * x for x in row] for row in a]

def mul(a, b):
    return [[sum(x*y for x, y in zip(row, col)) for col in zip(*b)] for row in a]

def integrate_blocks(generators, subset):
    """Integrate tr(b(t) U(t)) on three unit time intervals, at the stated order."""
    n = len(generators[0])
    outside = [i for i in range(n) if i not in subset]
    c_accum = zero(n)
    out = F(0)
    for a in reversed(generators):
        for i in subset:
            for k in outside:
                out += a[i][k] * (c_accum[k][i] + a[k][i] / 2)
                c_accum[k][i] += a[k][i]
    return out

def ordered_formula(generators, subset):
    outside = set(range(len(generators[0]))).difference(subset)
    return sum((F(1,2) if i == j else F(1)) * a[u][v] * b[v][u]
               for i, a in enumerate(generators)
               for j, b in enumerate(generators) if i <= j
               for u in subset for v in outside)

def det_coefficients(generators, subset):
    n = len(generators[0])
    linear, quadratic = zero(n), zero(n)
    for a in generators:
        quadratic = add(quadratic, add(mul(linear, a), scale(mul(a, a), F(1, 2))))
        linear = add(linear, a)
    identity = eye(n)
    z = [F(0), F(0), F(0)]
    for p in permutations(subset):
        inversions = sum(i > j for k, i in enumerate(p) for j in p[k+1:])
        value = [F((-1)**inversions), F(0), F(0)]
        for i, j in zip(subset, p):
            factor = [identity[i][j], linear[i][j], quadratic[i][j]]
            value = [sum(value[k]*factor[l-k] for k in range(l+1)) for l in range(3)]
        z = [a+b for a, b in zip(z, value)]
    return z

def check_constants():
    max_time, delta = F(3), F(1,20)
    exp_bound = 1 / (1-max_time*delta)  # e^s <= 1/(1-s)
    assert exp_bound <= F(6,5)
    assert exp_bound-1 <= F(1,5)
    inverse_bound = 1/(1-F(1,5))
    assert inverse_bound == F(5,4)
    assert inverse_bound*F(6,5) == F(3,2)
    graph_error = F(6,5)*inverse_bound + inverse_bound*F(6,5)
    assert graph_error == 3
    assert graph_error * max_time**3/3 == 27 < 10**4

def check_order_sensitivity():
    # Q=e11. Here tr(b1 c2)=1 while tr(b2 c1)=0.
    a, b = zero(2), zero(2)
    a[0][1] = b[1][0] = F(1)
    tests = [(a,b,zero(2)), (b,a,zero(2))]
    assert [integrate_blocks(t,[0]) for t in tests] == [1, 0]

def principal_det(a, subset):
    answer = F(0)
    for p in permutations(subset):
        term = F((-1)**sum(i > j for k, i in enumerate(p) for j in p[k+1:]))
        for i, j in zip(subset,p):
            term *= a[i][j]
        answer += term
    return answer

def log_interval(w):
    assert w > 0
    z = (w-1)/(w+1)
    terms = 5
    value = 2*sum(z**(2*j+1)/(2*j+1) for j in range(terms))
    error = 2*abs(z)**(2*terms+1)/((2*terms+1)*(1-z*z))
    return value-error, value+error

def check_complete_remainders():
    rng = Random(45319)
    count, witnessed = 0, 0
    for n in range(2,6):
        for sample in range(6):
            generators = []
            delta = F(1,40)
            y = eye(n)
            for j in range(3):
                u = [rng.choice([-1,1]) for _ in range(n)]
                v = [rng.randrange(-2,3) for _ in range(n-1)]
                v.append(-sum(a*b for a,b in zip(u,v))*u[-1])
                a = [[F(i*k,2000) for k in v] for i in u]
                assert mul(a,a) == zero(n)
                assert sum(entry**2 for row in a for entry in row) <= delta**2
                generators.append(a)
                y = mul(y,add(eye(n),a))
            for mask in range(1 << n):
                subset = [i for i in range(n) if mask & (1<<i)]
                l,h = log_interval(principal_det(y,subset))
                main = sum(a[i][i] for a in generators for i in subset)
                main += ordered_formula(generators,subset)
                l,h = l-main,h-main
                zeta_sq = max(sum(a[i][j]**2 for i in range(n) for j in range(n)
                                  if (i in subset) != (j in subset)) for a in generators)
                assert max(abs(l),abs(h)) <= 27*delta*zeta_sq
                count += 1
                witnessed += (l>0 or h<0)
    print(f"Full determinants with rational logarithm enclosures: {count}")
    print(f"Certified nonzero higher-order remainders among them: {witnessed}")

def run():
    rng = Random(20261127)
    checked = 0
    nonzero = 0
    for n in range(1,6):
        for sample in range(8):
            test = [[[F(rng.randint(-3,3), rng.randint(1,4)) for _ in range(n)]
                     for _ in range(n)] for _ in range(3)]
            for mask in range(1 << n):
                subset = [i for i in range(n) if mask & (1 << i)]
                constant, first, second = det_coefficients(test, subset)
                target_first = sum(a[i][i] for a in test for i in subset)
                target_second = ordered_formula(test, subset)
                assert constant == 1 and first == target_first
                assert second - first**2/2 == integrate_blocks(test, subset) == target_second
                nonzero += (target_second != 0)
                checked += 1
    print(f"Exact matrix/projection triples checked: {checked}")
    print(f"Triples with nonzero quadratic logarithm coefficient: {nonzero}")
    print("Forward/reversed order-sensitive examples: quadratic coefficients 1, 0")
    print("Rational estimate for the remainder coefficient: 27 (repository budget 10000)")
    print("All checks passed.")

if __name__ == "__main__":
    check_constants()
    check_order_sensitivity()
    check_complete_remainders()
    run()
