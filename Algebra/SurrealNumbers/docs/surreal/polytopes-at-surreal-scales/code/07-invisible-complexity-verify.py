#!/usr/bin/env python3
"""Exact finite checks for Invisible Complexity in Surreal Polytopes.

These checks validate identities and finite rational instances, NOT the
transcendence, real-closed-field, or all-orders theorems in the manuscript.
Requires Python 3.10+ and SymPy. Run from any directory.
"""
from __future__ import annotations

from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import json
import math
import platform
import sympy as sp

Point = tuple[F, F]


def det(a: Point, b: Point, c: Point) -> F:
    return (b[0]-a[0])*(c[1]-a[1]) - (b[1]-a[1])*(c[0]-a[0])


def symbolic_identities() -> dict:
    r, u, v, w = sp.symbols('r u v w')
    A, B = (r, 1-2*r), (1-2*r, r)
    C = lambda t: (r*t, r*(1-t)**2)
    D = lambda a,b,c: (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])
    tests = [
        (D(C(u), C(v), C(w)), r**2*(v-u)*(w-u)*(w-v)),
        (D(A, C(u), C(v)), r*(v-u)*(1+r*(u*v-u-v-1))),
        (D(C(u), C(v), B), r*(v-u)*(2-u-v+r*(u*v+2*u+2*v-4))),
        (D(A, C(u), B), (1-3*r)*(1-r*(u*u-u+2))),
    ]
    for lhs, rhs in tests:
        assert sp.expand(lhs-rhs) == 0
    N, x, y, lam = sp.symbols('N x y lam')
    R = (N-x, y+N*N-2*N*x)
    assert sp.expand(R[1] - R[0]**2).subs(y, x**2).expand() == 0
    assert sp.expand(x+(N-2*x)-R[0]) == 0
    assert sp.expand(y+N*(N-2*x)-R[1]) == 0
    return {'orientation_identities': len(tests), 'reflection_identities': 3}


def polygon(n: int, rho: F) -> list[Point]:
    if n < 4 or not (0 < rho < F(1, 10)):
        raise ValueError('Require n >= 4 and 0 < rho < 1/10.')
    k = n-2
    pts = [(rho, 1-2*rho)]
    for j in range(1, k+1):
        u = F(j, k+1)
        pts.append((rho*u, rho*(1-u)**2))
    pts.append((1-2*rho, rho))
    return pts


def finite_polygon_checks() -> dict:
    triples = 0
    slack_entries = 0
    for n in range(4, 37):
        rho = F(1, 100*n)
        q = polygon(n, rho)
        # Rational perturbations test stability only: they are not algebraically
        # independent and are not substitutes for the surreal perturbations.
        tau = rho**3 / (100*(n-1)**3)
        p = [(a+tau/F(2*i+3), b+tau/F(2*i+4))
             for i, (a,b) in enumerate(q)]
        for pts in (q, p):
            assert all(a > 0 and b > 0 and a+b < 1 for a,b in pts)
            for i,j,k in combinations(range(n), 3):
                assert det(pts[i], pts[j], pts[k]) > 0
                triples += 1
            for i in range(n):
                for j in range(n):
                    s = det(pts[i], pts[(i+1) % n], pts[j])
                    assert (s == 0) == (j in (i, (i+1) % n))
                    assert s >= 0
                    slack_entries += 1
            # Ordinary slack rank is 3, witnessed by a nonzero 3x3 minor.
            S = [[det(pts[i], pts[(i+1) % n], pts[j]) for j in range(3)]
                 for i in range(3)]
            # For n=4 this minor is nonzero as well.
            d = (S[0][0]*(S[1][1]*S[2][2]-S[1][2]*S[2][1])
                 - S[0][1]*(S[1][0]*S[2][2]-S[1][2]*S[2][0])
                 + S[0][2]*(S[1][0]*S[2][1]-S[1][1]*S[2][0]))
            assert d != 0
    return {'n_range': [4,36], 'positive_triples_checked': triples,
            'slack_entries_checked': slack_entries,
            'rational_instances_only': True}


def solve_square(A: list[list[F]], b: list[F]) -> tuple[F, ...] | None:
    """Small exact Gaussian elimination; None for singular matrices."""
    n = len(b)
    M = [list(row)+[rhs] for row, rhs in zip(A,b)]
    for col in range(n):
        pivot = next((i for i in range(col,n) if M[i][col]), None)
        if pivot is None:
            return None
        M[col], M[pivot] = M[pivot], M[col]
        z = M[col][col]
        M[col] = [a/z for a in M[col]]
        for i in range(n):
            if i == col:
                continue
            z = M[i][col]
            if z:
                M[i] = [a-z*c for a,c in zip(M[i], M[col])]
    return tuple(M[i][-1] for i in range(n))


def reflection_lift(N: int):
    """Return inequalities A z <= b and the affine output (x,y).

    Binary reflection recursion starts at the point (0,0). At stage M it
    introduces lambda satisfying 0 <= lambda <= M - 2*x_old, and outputs
    (x_old+lambda, y_old+M*lambda). Constants of x,y stay zero.
    """
    chain = []
    q = N
    while q:
        chain.append(q)
        q //= 2
    chain.reverse()
    d = len(chain)
    x, y = [F(0)]*d, [F(0)]*d
    A: list[list[F]] = []
    b: list[F] = []
    for t, M in enumerate(chain):
        lo = [F(0)]*d
        lo[t] = -1
        hi = [2*c for c in x]
        hi[t] += 1
        A.extend([lo, hi])
        b.extend([F(0), F(M)])
        x[t] += 1
        y[t] += M
    return A, b, x, y


def reflection_checks() -> dict:
    total_bases = total_vertices = 0
    for N in range(1, 32):
        A,b,x,y = reflection_lift(N)
        d = len(x)
        assert len(A) == 2*N.bit_length()
        images = set()
        vertices = set()
        for I in combinations(range(len(A)), d):
            z = solve_square([A[i] for i in I], [b[i] for i in I])
            total_bases += 1
            if z is None:
                continue
            if any(sum(a*t for a,t in zip(row,z)) > rhs
                   for row,rhs in zip(A,b)):
                continue
            vertices.add(z)
            images.add((sum(a*t for a,t in zip(x,z)),
                        sum(a*t for a,t in zip(y,z))))
        target = {(F(j), F(j*j)) for j in range(N+1)}
        assert images == target, (N, images-target, target-images)
        total_vertices += len(vertices)
    for N in range(1, 257):
        m = N//2
        assert set(range(m+1)) | {N-j for j in range(m+1)} == set(range(N+1))
    return {'enumerated_N_range': [1,31], 'active_bases_checked': total_bases,
            'distinct_lift_vertices_total': total_vertices,
            'reflection_index_checks': 256}


def leading_slack_checks() -> dict:
    r = sp.symbols('r')
    checked = 0
    orders = set()
    for n in range(4, 13):
        k = n-2
        pts = [(r,1-2*r)] + [(r*sp.Rational(j,k+1),
              r*(1-sp.Rational(j,k+1))**2) for j in range(1,k+1)] + [(1-2*r,r)]
        for i in range(n):
            for j in range(n):
                a, b, c = pts[i], pts[(i+1)%n], pts[j]
                expr = ((b[0]-a[0])*(c[1]-a[1])
                        - (b[1]-a[1])*(c[0]-a[0]))
                s = sp.Poly(sp.expand(expr), r)
                if j in (i,(i+1)%n):
                    assert s.is_zero
                else:
                    terms = s.terms()
                    deg, coeff = min((mon[0], coeff) for mon,coeff in terms)
                    assert coeff > 0 and deg in (0,1,2)
                    orders.add(deg)
                checked += 1
    return {'symbolic_slack_entries': checked, 'nonzero_leading_orders': sorted(orders)}


def normalization_checks() -> dict:
    U = sp.Matrix([[1,2,0],[3,1,2],[2,0,1]])
    V = sp.Matrix([[2,3],[1,4],[5,2]])
    sums = [sum(U[:,i]) for i in range(U.cols)]
    T = sp.diag(*sums)
    C, D = U*T.inv(), T*V
    assert C*D == U*V
    assert all(sum(C[:,i]) == 1 for i in range(C.cols))
    M = U*V
    assert all(0 <= D[a,j] <= sum(M[:,j]) for a in range(D.rows) for j in range(D.cols))
    # A congruence check, not a computational verification of spectral theory.
    H = sp.Matrix([[2,1],[0,3]])
    Ai = sp.Matrix([[2,1],[1,1]])
    Bj = sp.Matrix([[3,1],[1,2]])
    Ci = H*Ai*H.T
    Dj = H.T.inv()*Bj*H.inv()
    assert sp.trace(Ci*Dj) == sp.trace(Ai*Bj)
    return {'nonnegative_column_normalization': True, 'psd_trace_congruence': True}


def complexity_table() -> list[dict]:
    out = []
    for m in [8,12,16,20,24]:
        n = 2**m+2
        lp = math.isqrt(2*n)
        while lp*(lp-1) < 2*n:
            lp += 1
        psd = 1
        while (psd*(psd+1)//2)**2 < 2*n:
            psd += 1
        out.append({'n': n, 'easy_LP_and_PSD_upper': 2*m+2,
                    'hard_LP_lower': lp, 'hard_PSD_lower': psd})
    return out


def main() -> None:
    results = {
        'status': 'all finite checks passed',
        'scope': 'Finite exact checks only; not a formal proof of the manuscript.',
        'python': platform.python_version(), 'sympy': sp.__version__,
        'identities': symbolic_identities(),
        'polygons': finite_polygon_checks(),
        'reflection_lifts': reflection_checks(),
        'slack_initial_forms': leading_slack_checks(),
        'normalizations': normalization_checks(),
        'complexity_bounds': complexity_table(),
    }
    dest = Path(__file__).resolve().with_name('results.json')
    dest.write_text(json.dumps(results, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(results, indent=2))


if __name__ == '__main__':
    main()
