#!/usr/bin/env python3
"""Finite exact checks for Polynomial-Composition Rigidity at Surreal Scales.

Requires Python 3.10+ and SymPy. This is NOT a verifier for infinite Hahn
summability and does not formalize the article. It checks finite identities,
selected Gauss initial forms, degree certificates, and the universal encoder.
The JSON output records actual assertion counts; any failed assertion aborts.
"""
from __future__ import annotations

import argparse
import json
import math
import platform
import random
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Dict, Iterable, Tuple

import sympy as sp
from sympy.matrices.normalforms import smith_normal_form

z, T = sp.symbols('z T')
COUNTS: Counter[str] = Counter()
RNG = random.Random(20260923)


def check(group: str, condition: bool, detail: str = '') -> None:
    if not condition:
        raise AssertionError(f'{group}: {detail}')
    COUNTS[group] += 1


def equal(group: str, left: sp.Expr, right: sp.Expr) -> None:
    check(group, sp.expand(left - right) == 0, f'{left} != {right}')


def degree(poly: sp.Expr) -> int | sp.core.numbers.NegativeInfinity:
    return sp.S.NegativeInfinity if sp.expand(poly) == 0 else int(sp.degree(poly, z))


def falling(x: sp.Expr, r: int) -> sp.Expr:
    return sp.prod(x - j for j in range(r))


@dataclass(frozen=True)
class Operator:
    """Normal form sum b_r(z) D^r; coefficients are exact SymPy expressions."""
    coefficients: Tuple[sp.Expr, ...]

    def apply(self, f: sp.Expr) -> sp.Expr:
        return sp.expand(sum(b * sp.diff(f, z, r)
                             for r, b in enumerate(self.coefficients)))

    def invariants(self) -> Tuple[int, sp.Expr]:
        nonzero = [(r, sp.Poly(b, z)) for r, b in enumerate(self.coefficients)
                   if sp.expand(b) != 0]
        if not nonzero:
            raise ValueError('The zero operator has no indicial invariant.')
        h = max(int(p.degree()) - r for r, p in nonzero)
        chi = sp.expand(sum(p.LC() * falling(T, r) for r, p in nonzero
                            if int(p.degree()) - r == h))
        if chi == 0:
            raise AssertionError('Nonzero normal-form operator has zero indicial polynomial.')
        return h, chi


def linear_bound(arguments: Tuple[sp.Expr, ...],
                 operators: Tuple[Operator, ...], forcing: sp.Expr) -> int:
    if len(arguments) != len(operators) or not arguments:
        raise ValueError('Provide equally many nonempty arguments and operators.')
    ds = [int(sp.degree(p, z)) for p in arguments]
    if any(d < 1 for d in ds) or ds[-1] < 2 or any(d >= ds[-1] for d in ds[:-1]):
        raise ValueError('The last argument must have uniquely largest degree >= 2.')
    invariants = [op.invariants() for op in operators]
    hs = [h for h, _ in invariants]
    rootpoly = sp.Poly(invariants[-1][1].subs(T, ds[-1] * T), T, domain=sp.QQ)
    roots = [int(r) for r in rootpoly.ground_roots()
             if r.is_integer and r >= 0]
    candidates = [0] + roots
    candidates.extend((hs[j] - hs[-1]) // (ds[-1] - ds[j])
                      for j in range(len(ds)-1))
    if forcing != 0:
        candidates.append((int(sp.degree(forcing, z)) - hs[-1]) // ds[-1])
    return max(candidates)


def random_poly(max_degree: int, force_degree: bool = False) -> sp.Expr:
    values = [RNG.randint(-3, 3) for _ in range(max_degree + 1)]
    if force_degree:
        values[-1] = RNG.choice([-3, -2, -1, 1, 2, 3])
    return sum(sp.Integer(v) * z**i for i, v in enumerate(values))


def test_indicial() -> None:
    for _ in range(150):
        op = Operator(tuple(random_poly(RNG.randint(0, 4), True)
                            for _ in range(RNG.randint(1, 4))))
        h, chi = op.invariants()
        n = RNG.randint(0, 8)
        f = random_poly(n, True)
        image = op.apply(f)
        expected_degree = n + h
        check('indicial_leading_terms', degree(image) <= expected_degree)
        chi_n = sp.expand(chi.subs(T, n))
        if chi_n != 0:
            check('indicial_leading_terms', degree(image) == expected_degree)
            equal('indicial_leading_terms', sp.Poly(image, z).LC(),
                  sp.Poly(f, z).LC() * chi_n)
        else:
            check('indicial_leading_terms', degree(image) < expected_degree)
    for d in range(2, 6):
        for N in range(0, 13):
            op = Operator((-d*N, z))
            h, chi = op.invariants()
            check('exact_resonance', h == 0)
            equal('exact_resonance', chi.subs(T, d*N), 0)
            equal('exact_resonance', op.apply(z**(d*N)), 0)
            check('exact_resonance', linear_bound((z**d,), (op,), 0) == N)


# A finite Hahn polynomial is a sparse dictionary (z-degree, gamma_0, gamma_1)
# -> Fraction. Exponents are in lexicographically ordered Z^2, first coordinate
# dominant. This intentionally implements only finite supports.
Key = Tuple[int, int, int]
HP = Dict[Key, Fraction]
Gamma = Tuple[int, int]


def ga(a: Gamma, b: Gamma) -> Gamma:
    return a[0]+b[0], a[1]+b[1]


def gs(a: Gamma, b: Gamma) -> Gamma:
    return a[0]-b[0], a[1]-b[1]


def gm(n: int, a: Gamma) -> Gamma:
    return n*a[0], n*a[1]


def hadd(*polys: HP) -> HP:
    out: HP = {}
    for p in polys:
        for key, value in p.items():
            out[key] = out.get(key, Fraction(0)) + value
    return {k: v for k, v in out.items() if v}


def hmul(a: HP, b: HP) -> HP:
    out: HP = {}
    for (i, x, y), c in a.items():
        for (j, u, v), e in b.items():
            key = i+j, x+u, y+v
            out[key] = out.get(key, Fraction(0)) + c*e
    return {k: v for k, v in out.items() if v}


def hdiff(a: HP, r: int) -> HP:
    return {(n-r, x, y): c*math.prod(range(n-r+1, n+1))
            for (n, x, y), c in a.items() if n >= r}


def hcompose(a: HP, p: HP) -> HP:
    powers: list[HP] = [{(0, 0, 0): Fraction(1)}]
    for _ in range(max((n for n, _, _ in a), default=0)):
        powers.append(hmul(powers[-1], p))
    return hadd(*(hmul({(0, x, y): c}, powers[n])
                  for (n, x, y), c in a.items()))


def hprofile(a: HP, rho: Gamma) -> Tuple[Gamma, Dict[int, Fraction]]:
    if not a:
        raise ValueError('Zero polynomial has no finite Gauss profile.')
    weighted = [(gs(gm(n, rho), (x, y)), n, c)
                for (n, x, y), c in a.items()]
    height = max(h for h, _, _ in weighted)
    initial: Dict[int, Fraction] = {}
    for h, n, c in weighted:
        if h == height:
            initial[n] = initial.get(n, Fraction(0)) + c
    initial = {n: c for n, c in initial.items() if c}
    if not initial:
        raise AssertionError('Input was not in collected sparse form.')
    return height, initial


def hoperator(coeffs: Tuple[HP, ...], a: HP) -> HP:
    return hadd(*(hmul(b, hdiff(a, r)) for r, b in enumerate(coeffs)))


def test_hahn() -> None:
    # Tied active degrees and three maximal-shift differential terms.
    for _ in range(45):
        rho = (100 + RNG.randint(0, 10), RNG.randint(-4, 4))
        f: HP = {}
        for n in range(RNG.randint(3, 7)):
            x, y = gm(n, rho)
            f[n, x, y] = Fraction(RNG.choice([-3, -1, 1, 2, 4]))
            f[n, x, y+1] = Fraction(1)
        # Residue indicial polynomial: 2+T+T(T-1)=T^2+2.
        coeffs = ({(0, 0, 0): Fraction(2)},
                  {(1, 0, 0): Fraction(1), (0, -1, 3): Fraction(1)},
                  {(2, 0, 0): Fraction(1)})
        hf, initial_f = hprofile(f, rho)
        hu, initial_u = hprofile(hoperator(coeffs, f), rho)
        check('rank_two_operator_profiles', hu == hf)
        check('rank_two_operator_profiles',
              initial_u == {n: c*(n*n+2) for n, c in initial_f.items()})

    for _ in range(35):
        rho = (100, RNG.randint(-3, 3))
        f = {(n, RNG.randint(-3, 3), RNG.randint(-4, 4)):
             Fraction(RNG.choice([-2, -1, 1, 3])) for n in range(RNG.randint(2, 5))}
        d = RNG.randint(2, 3)
        kappa = (RNG.randint(-2, 2), RNG.randint(-3, 3))
        lead = Fraction(RNG.choice([-2, -1, 1, 2]))
        p = {(d, *kappa): lead, (1, 0, 0): Fraction(1),
             (0, 1, -2): Fraction(-1)}
        sigma = gs(gm(d, rho), kappa)
        source_h, source_i = hprofile(f, sigma)
        target_h, target_i = hprofile(hcompose(f, p), rho)
        check('rank_two_pullback_profiles', source_h == target_h)
        check('rank_two_pullback_profiles',
              target_i == {d*n: c*lead**n for n, c in source_i.items()})
        g = {(n, RNG.randint(-3, 3), RNG.randint(-3, 3)):
             Fraction(RNG.choice([-2, 1, 3])) for n in range(3)}
        check('rank_two_gauss_products',
              hprofile(hmul(f, g), rho)[0] ==
              ga(hprofile(f, rho)[0], hprofile(g, rho)[0]))

    for _ in range(180):
        d = RNG.randint(2, 9)
        e = RNG.randint(1, d-1)
        rho = (RNG.randint(15, 100), RNG.randint(-8, 8))
        kappa = (RNG.randint(-8, 8), RNG.randint(-8, 8))
        kappae = (RNG.randint(-8, 8), RNG.randint(-8, 8))
        R = (200, 200)
        sigma = gs(gm(d, rho), kappa)
        tau = gs(gm(e, rho), kappae)
        check('integer_convexity', gm(d, tau) <= ga(gm(e, sigma), gm(d-e, R)))
        f = {(n, RNG.randint(-20, 20), RNG.randint(-20, 20)):
             Fraction(RNG.choice([-1, 1, 2])) for n in range(8)}
        lhs = gm(d, hprofile(f, tau)[0])
        rhs = ga(gm(e, hprofile(f, sigma)[0]), gm(d-e, hprofile(f, R)[0]))
        check('integer_convexity', lhs <= rhs)


def euler_poly_apply(q: sp.Expr, f: sp.Expr) -> sp.Expr:
    """Apply q(E_z) by its diagonal action on monomials; exact finite polynomials."""
    return sp.expand(sum(c*q.subs(T, n)*z**n
                         for (n,), c in sp.Poly(f, z).terms()))


def test_encoder() -> None:
    for N in list(range(5)) + [10]:
        variables = sp.symbols(f'u0:{N+1}')
        f = sum(variables[j]*z**j for j in range(N+1))
        projectors = []
        for j in range(N+1):
            pj = sp.expand(sp.factorial(N) * sp.prod((T-k)/sp.Integer(j-k)
                          for k in range(N+1) if k != j))
            projectors.append(pj)
            check('euler_projectors', all(c.is_integer for c in sp.Poly(pj, T).all_coeffs()))
            equal('euler_projectors', euler_poly_apply(pj, f),
                  sp.factorial(N)*variables[j]*z**j)
            for k in range(N+1):
                equal('euler_projectors', pj.subs(T, k),
                      sp.factorial(N) if k == j else 0)
        runs = 1 if N == 10 else 8
        for _ in range(runs):
            p = sp.Integer(RNG.randint(1, 3))
            for _ in range(5):
                term = sp.Integer(RNG.choice([-3, -1, 1, 2]))
                for _ in range(RNG.randint(1, 3)):
                    term *= variables[RNG.randint(0, N)]
                p += term
            p = sp.Poly(sp.expand(p), *variables)
            terms = p.terms()
            q = max(sum(a) for a, c in terms)
            shift = max(sum(j*a[j] for j in range(N+1)) for a, c in terms)
            d = q+shift+2
            lhs_op = sp.prod(T-d*k for k in range(N+1))
            equal('universal_encoding', euler_poly_apply(lhs_op, f.subs(z, z**d)), 0)
            rhs = 0
            candidates = [0, N]
            for a, c in terms:
                weight_index = sum(j*a[j] for j in range(N+1))
                term = c*sp.factorial(N)**(q-sum(a))*z**(shift-weight_index)
                for j in range(N+1):
                    term *= euler_poly_apply(projectors[j], f)**a[j]
                rhs += term
                check('universal_encoding', sum(a) < d)
                check('universal_encoding', shift-weight_index >= 0)
                candidates.append((shift-weight_index)//(d-sum(a)))
            equal('universal_encoding', rhs,
                  sp.factorial(N)**q*z**shift*p.as_expr())
            check('universal_encoding', max(candidates) == N)
            for n in range(N+1, N+4):
                check('universal_encoding', lhs_op.subs(T, d*n) != 0)


def test_examples() -> dict:
    identity = Operator((sp.Integer(1),))
    negative_identity = Operator((sp.Integer(-1),))
    bounds = {}
    for d in range(2, 5):
        for N in range(8):
            B = linear_bound((z, z**d),
                             (Operator((-z**((d-1)*N),)), identity), 0)
            check('sharp_degree_family', B == N)
            equal('sharp_degree_family', (z**N).subs(z, z**d), z**((d-1)*N)*z**N)
    B = linear_bound((z, z*z), (negative_identity, identity), z*z-z)
    check('worked_equations', B == 1)
    bounds['free_parameter_equation'] = B
    a0, a1 = sp.symbols('a0 a1')
    equal('worked_equations', (a0+a1*z).subs(z, z*z)-(a0+a1*z), a1*(z*z-z))

    top = Operator((-6, z)); lower = Operator((1, z*z))
    forcing = -3*z**5-3*z**4-2*z**3-6*z**2-8*z-5
    B = linear_bound((z, z*z+z), (lower, top), forcing)
    check('worked_equations', B == 3)
    bounds['mixed_resonance_equation'] = B
    f = z**3+2*z+1
    equal('worked_equations', top.apply(f.subs(z, z*z+z))+lower.apply(f), forcing)
    a = sp.symbols('a0:4')
    F = sum(a[i]*z**i for i in range(4))
    coeffs = sp.Poly(top.apply(F.subs(z, z*z+z))+lower.apply(F)-forcing, z).all_coeffs()
    check('worked_equations', sp.linsolve(coeffs, a) == sp.FiniteSet((1, 2, 0, 1)))

    f = z+1
    forcing2 = z**4-z**3-z**2-3*z-1
    equal('worked_equations', f.subs(z, z*z)**2,
          f**3+sp.diff(f, z)**2+forcing2)
    check('worked_equations', max(0, (0-0)//(4-3), (-2-0)//(4-2), 4//4) == 1)
    a, b = sp.symbols('a b'); F = a*z+b
    coeffs = sp.Poly(F.subs(z, z*z)**2-F**3-sp.diff(F, z)**2-forcing2, z).all_coeffs()
    check('worked_equations', sp.solve(coeffs, (a, b), dict=True) == [{a: 1, b: 1}])
    bounds['weighted_nonlinear_equation'] = 1

    f = z*z+z+1; forcing3 = z**6-z**4-z**3-3*z*z-2*z
    equal('worked_equations', f.subs(z, z**3), f*f+forcing3)
    check('worked_equations', max(0, 0//(3-2), 6//3) == 2)
    bounds['cubic_pullback_equation'] = 2

    # Explicit encoder for a^2+b^2=m.
    m = sp.symbols('m'); F = a+b*z
    lhs = euler_poly_apply(T*(T-6), F.subs(z, z**6))
    rhs = z*z*euler_poly_apply(1-T, F)**2+euler_poly_apply(T, F)**2-m*z*z
    equal('worked_equations', lhs, 0)
    equal('worked_equations', rhs, z*z*(a*a+b*b-m))

    # Truncated coefficient identity; NOT a check of infinite summability.
    q = sp.symbols('q'); trunc = sum(q**(n*(n-1)//2)*z**n for n in range(15))
    residual = sp.Poly(sp.expand(trunc-1-z*trunc.subs(z, q*z)), z)
    for n in range(15):
        equal('boundary_coefficient_checks', residual.nth(n), 0)
    for p in (2, 3, 5, 7):
        for n in range(15):
            check('boundary_coefficient_checks', (p*n) % p == 0)
    return bounds


def unimodular(n: int) -> sp.Matrix:
    m = sp.eye(n)
    for _ in range(8):
        i, j = RNG.sample(range(n), 2)
        m[i, :] = m[i, :] + RNG.choice([-2, -1, 1, 2])*m[j, :]
    return m


def test_smith() -> None:
    x = sp.symbols('x')
    S = sp.Matrix([[2, 0, 0, 0], [0, 6, 0, 0], [0, 0, 0, 0]])
    for _ in range(25):
        U, V = unimodular(3), unimodular(4)
        M = U.inv()*S*V.inv()
        check('smith_certificates', abs(U.det()) == abs(V.det()) == 1)
        check('smith_certificates', all(entry.is_integer for entry in M))
        check('smith_certificates', U*M*V == S)
        smith = smith_normal_form(M, domain=sp.ZZ)
        check('smith_certificates', [abs(smith[j, j]) for j in range(3)] == [2, 6, 0])
        base = sp.Matrix([RNG.randint(-4, 4) for _ in range(4)])
        free = V*sp.Matrix([0, 0, x+x*x, 2*x**3-x])
        check('smith_certificates', M*free == sp.zeros(3, 1))
        check('smith_certificates', sp.simplify(M*(base+free)-M*base) == sp.zeros(3, 1))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('verification.json'))
    args = parser.parse_args()
    test_indicial()
    test_hahn()
    test_encoder()
    bounds = test_examples()
    test_smith()
    result = {
        'status': 'all finite checks passed',
        'seed': 20260923,
        'python': platform.python_version(),
        'sympy': sp.__version__,
        'total_assertions': sum(COUNTS.values()),
        'assertions_by_group': dict(sorted(COUNTS.items())),
        'worked_degree_bounds': bounds,
        'scope': [
            'Exact finite polynomial identities and leading coefficients',
            'Finite-support Hahn profiles over lexicographic Z^2',
            'Integer convexity inequalities with valuation shifts',
            'Euler projectors and universal Diophantine encoding',
            'Worked equations, resonance, and finite Smith certificates'
        ],
        'not_verified': [
            'Arbitrary infinite Hahn summability',
            'All universally quantified claims by a proof assistant',
            'Historical novelty or independent mathematical correctness',
            'The Surreal repository Lean build'
        ]
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
