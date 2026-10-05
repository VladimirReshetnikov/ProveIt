#!/usr/bin/env python3
"""Finite exact weight-8/10/12 brackets and second-correction algebra.

Standard library only. This finite proof certificate uses the manuscript's
Bloch--Okounkov span theorem and transfer theorem as analytic inputs; it does
not re-prove them or implement a general all-orders symbolic engine.
"""
from fractions import Fraction as F
from itertools import product
import json
N = 20


def need(condition, message):
    if not condition:
        raise ValueError(message)


def partitions(n, maximum=None):
    if n == 0:
        yield ()
        return
    maximum = n if maximum is None else min(n, maximum)
    for k in range(maximum, 0, -1):
        for tail in partitions(n-k, k):
            yield (k,) + tail


def multiply(a, b):
    need(len(a) == len(b) == N+1, 'series lengths must equal N+1')
    return [sum((a[k]*b[n-k] for k in range(n+1)), F(0))
            for n in range(N+1)]


def power(a, k):
    need(type(k) is int and k >= 0, 'power must be a nonnegative integer')
    out = [F(1)] + [F(0)]*N
    for _ in range(k):
        out = multiply(out, a)
    return out


def solve(matrix, rhs):
    """Exact pivoted Gaussian elimination; return solution and determinant."""
    n = len(matrix)
    need(n > 0 and len(rhs) == n and all(len(row) == n for row in matrix),
         'system must be square and nonempty')
    augmented = [[F(value) for value in row] + [F(rhs[i])]
                 for i, row in enumerate(matrix)]
    determinant = F(1)
    for j in range(n):
        pivot = next((i for i in range(j, n) if augmented[i][j]), None)
        need(pivot is not None, 'singular initial coefficient matrix')
        if pivot != j:
            augmented[j], augmented[pivot] = augmented[pivot], augmented[j]
            determinant = -determinant
        factor = augmented[j][j]
        determinant *= factor
        augmented[j] = [x/factor for x in augmented[j]]
        for i in range(n):
            if i != j:
                factor = augmented[i][j]
                augmented[i] = [x-factor*y for x, y in zip(augmented[i], augmented[j])]
    return [row[-1] for row in augmented], determinant


def add(*polynomials):
    out = {}
    for polynomial in polynomials:
        for key, value in polynomial.items():
            out[key] = out.get(key, F(0)) + value
    return {key: value for key, value in out.items() if value}


def scale(polynomial, scalar):
    return {key: value*scalar for key, value in polynomial.items() if value*scalar}


def mul(a, b):
    out = {}
    for ka, va in a.items():
        for kb, vb in b.items():
            need(len(ka) == len(kb), 'polynomial bases differ')
            key = tuple(x+y for x, y in zip(ka, kb))
            out[key] = out.get(key, F(0)) + va*vb
    return {key: value for key, value in out.items() if value}


def pow_poly(a, k, dimensions):
    need(type(k) is int and k >= 0, 'polynomial power must be nonnegative')
    out = {(0,)*dimensions: F(1)}
    for _ in range(k):
        out = mul(out, a)
    return out


def terms(polynomial):
    return [{'powers': list(key), 'coefficient': str(value)}
            for key, value in sorted(polynomial.items())]


def derive():
    p = [0]*(N+1)
    raw = [[F(0)]*(N+1) for _ in range(3)]
    for n in range(N+1):
        for partition in partitions(n):
            p[n] += 1
            def shifted(j):
                return F(sum((2*v-2*i+1)**j-(-2*i+1)**j
                             for i, v in enumerate(partition, 1)), 2**j)
            q2, u = shifted(2), shifted(3) + F(7, 960)
            for row, value in zip(raw, (u*u, q2*q2*u, q2**4)):
                row[n] += value
    inverse = [F(1)] + [F(0)]*N
    for n in range(1, N+1):
        inverse[n] = -sum((p[k]*inverse[n-k] for k in range(1, n+1)), F(0))
    need(multiply(p, inverse) == [F(1)] + [F(0)]*N, 'partition series inversion')
    eisenstein = []
    for weight, factor in ((2, -24), (4, 240), (6, -504)):
        series = [F(1)] + [F(0)]*N
        for d in range(1, N+1):
            for n in range(d, N+1, d):
                series[n] += factor*d**(weight-1)
        eisenstein.append(series)
    # Laurent basis is (power of t, power of pi).
    substitution = [{(-2, 2): F(-4), (-1, 0): F(12)},
                    {(-4, 4): F(16)}, {(-6, 6): F(-64)}]
    expected = {
        8: (['73/179200', '1/4032', '-1/5120', '-5/12288'],
            '-17336861982720', {(-8,8):F(49,3600),(-7,6):F(571,420),(-6,4):F(-243,40),(-5,2):F(45,4),(-4,0):F(-135,16)}),
        10: (['-301/1555200', '49/1036800', '119/622080', '119/1244160', '-35/248832'],
             '3559021983729451008000', {(-9,8):F(28,675),(-8,6):F(77,9),(-7,4):F(-1631,45),(-6,2):F(175,3),(-5,0):F(-35)}),
        12: (['151/3499200', '7/93312', '-149/1166400', '-199/1555200', '29/699840', '37/233280', '-35/559872'],
             '-124747187309624027471021601904499097600000', {(-10,8):F(256,675),(-9,6):F(8576,135),(-8,4):F(-11632,45),(-7,2):F(1120,3),(-6,0):F(-560,3)})}
    brackets = {}
    for weight, numerator in zip((8, 10, 12), raw):
        bracket = multiply(numerator, inverse)
        basis = [(a,b,c) for a in range(weight//2+1) for b in range(weight//4+1)
                 for c in range(weight//6+1) if 2*a+4*b+6*c == weight]
        columns = [multiply(multiply(power(eisenstein[0],a), power(eisenstein[1],b)),
                            power(eisenstein[2],c)) for a,b,c in basis]
        matrix = [[column[n] for column in columns] for n in range(len(basis))]
        coefficients, determinant = solve(matrix, bracket[:len(basis)])
        need([str(x) for x in coefficients] == expected[weight][0], 'bracket coefficients')
        need(str(determinant) == expected[weight][1], 'initial determinant')
        for n in range(N+1):
            need(sum((coefficient*column[n] for coefficient, column in zip(coefficients, columns)),F(0))
                 == bracket[n], 'q-bracket coefficient at q^' + str(n))
        laurent = {}
        for coefficient, exponents in zip(coefficients, basis):
            monomial = {(0,0): F(1)}
            for expression, exponent in zip(substitution, exponents):
                monomial = mul(monomial, pow_poly(expression, exponent, 2))
            laurent = add(laurent, scale(monomial, coefficient))
        need(laurent == expected[weight][2], 'complete Laurent substitution')
        brackets[str(weight)] = {'basis_E2_E4_E6': [list(v) for v in basis],
            'coefficients': [str(v) for v in coefficients],
            'initial_determinant': str(determinant),
            'laurent_basis': ['t','pi'], 'laurent': terms(laurent),
            'q_coefficients_checked': N+1}
    # Transfer rational factors. sqrt(6)/pi=2/b and 1/pi^2=2/(3b^2).
    leading = [F(49,3600)*6**4, F(28,675)*6**4, F(256,675)*6**5]
    need(leading == [F(441,25), F(1344,25), F(73728,25)], 'leading mixed moments')
    next_q3 = -F(7,60)*36-F(1,2)*6
    next_q22 = -F(5,2)*F(16,45)*216-F(4,3)*36
    need(next_q3 == -F(36,5) and next_q22 == -240, 'Bessel next-moment factors')
    # All subsequent polynomials use basis (z=m^-1/2, x=sqrt(c), b, mu, mu2).
    def mono(value,z=0,x=0,b=0,mu=0,mu2=0):
        return {(z,x,b,mu,mu2): F(value)}
    f2=add(mono(-F(1,4),z=3,b=1),mono(1,z=4))
    f3=add(mono(F(3,8),z=5,b=1),mono(-2,z=6))
    q3=add(mono(F(21,5),z=-4,x=4),mono(-F(72,5),z=-3,x=3,b=-1))
    q22=add(mono(F(128,5),z=-5,x=5,b=-1),mono(-160,z=-4,x=4,b=-2))
    q33=mono(F(441,25),z=-8,x=8)
    q223=mono(F(2688,25),z=-9,x=9,b=-1)
    q24=mono(F(49152,25),z=-10,x=10,b=-2)
    expansion=add(scale(mul(f3,q3),F(1,6)),scale(mul(pow_poly(f2,2,5),q22),F(1,8)),
                  scale(mul(pow_poly(f3,2,5),q33),F(1,72)),
                  scale(mul(mul(pow_poly(f2,2,5),f3),q223),F(1,48)),
                  scale(mul(pow_poly(f2,4,5),q24),F(1,384)))
    need(all(key[0]>=1 for key in expansion),'unexpected correction order')
    def at_order(order):
        return {(0,)+key[1:]:value for key,value in expansion.items() if key[0]==order}
    A1=add(mono(F(21,80),x=4,b=1),mono(F(1,5),x=5,b=1))
    lower=add(mono(-F(9,10),x=3),mono(-F(53,20),x=4),mono(-F(8,5),x=5))
    A2=add(scale(mul(A1,A1),F(1,2)),lower)
    need(at_order(1)==A1 and at_order(2)==A2,'A1/A2 extraction')
    d0=add(mono(F(1,2),b=1),mono(F(1,2),x=-1,b=1))
    d1=add(mono(-1),mono(-1,x=-2))
    mu,mu2=mono(1,mu=1),mono(1,mu2=1)
    B1=add(A1,mul(mu,d0))
    B2=add(A2,mul(mu,add(d1,mul(d0,A1))),scale(mul(mu2,mul(d0,d0)),F(1,2)))
    variance=add(mu2,scale(mul(mu,mu),-1))
    compact=add(scale(mul(B1,B1),F(1,2)),lower,mul(mu,d1),scale(mul(variance,mul(d0,d0)),F(1,2)))
    need(B2==compact,'B2 variance identity')
    return {'status':'PASS','report':182,'scope':{
        'exact_finite_quasimodular_reconstruction':True,'general_all_orders_symbolic_engine':False,
        'Bloch_Okounkov_span_theorem_assumed_from_manuscript':True,
        'analytic_transfer_and_remainders_certified_by_code':False,
        'effective_asymptotic_onset_certified':False,'finite_n_accuracy_theorem':False},
        'partition_enumeration_through':N,'partitions_enumerated':sum(p),'brackets':brackets,
        'leading_moment_rational_factors':[str(v) for v in leading],
        'next_moment_rational_factors':[str(next_q3),str(next_q22)],
        'correction_basis':['m^(-1/2)','sqrt(c)','b','mean_hole_energy','second_moment_hole_energy'],
        'A1':terms(A1),'A2':terms(A2),'B1':terms(B1),'B2':terms(B2),
        'B2_variance_identity_exact':True}


if __name__ == '__main__':
    print(json.dumps(derive(),sort_keys=True,indent=2))
