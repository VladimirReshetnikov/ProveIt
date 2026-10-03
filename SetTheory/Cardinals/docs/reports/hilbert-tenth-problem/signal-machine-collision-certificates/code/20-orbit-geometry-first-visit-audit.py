#!/usr/bin/env python3
"""Finite algebra fixtures only, not a CA/QE compiler or substitute for proof."""
from itertools import product
from fractions import Fraction
import json
import sympy as s

COUNTS = {}
def require(test, message):
    if not test:
        raise RuntimeError(message)

def split(q):
    return max(q, 0), max(-q, 0)

def expected(x, y):
    if x >= 0 and y == 0 and x % 2 == 1:
        return 0, (x*x+1)//2
    if x < 0 and x+y == 0 and x % 3 == 1:
        return 1, (x*x+x)//2
    return None

def canonical(x, y):
    result = expected(x, y)
    if result is None:
        return None
    branch, t = result
    if branch == 0:
        a, b = split((x-1)//2)
        w = (1, 0, x, 0, a, b, 0, 0)
    else:
        a, b = split((x-1)//3)
        w = (0, 1, 0, -x-1, 0, 0, a, b)
    return w, (x*x, y*y, (x+y)**2), t

def residuals(x, y, w):
    e, f, u, v, p, n, q, m = w
    return (e+f-1, e*x-u, f*(-x-1)-v, e*y, f*(x+y),
            e*(x-1)-2*(p-n), p*n, f*(x-1)-3*(q-m), q*m)

def timed_residuals(x, y, t, w, U):
    a, b, c = U
    e, f = w[:2]
    return residuals(x, y, w) + (a-x*x, b-y*y, c-(x+y)**2,
                                4*t-e*(2*a+2)-f*(a+b+c+2*x))

# Explicit failing-guard self-test remains active under python -O.
try:
    require(False, 'deliberate guard failure')
except RuntimeError:
    COUNTS['guard_self_test'] = 1
else:
    raise RuntimeError('guard self-test did not fail')

# Symbolic total degree is measured jointly in external and witness variables.
x, y, t = s.symbols('x y t')
w = s.symbols('e f u v p n q m')
U = s.symbols('U1 U2 U12')
P = sum(r*r for r in residuals(x, y, w))
Pt = sum(r*r for r in timed_residuals(x, y, t, w, U))
require(s.Poly(P, x, y, *w).total_degree() == 4, 'membership degree')
require(s.Poly(Pt, x, y, t, *w, *U).total_degree() == 4, 'timed degree')
require(all(c.is_Integer for c in s.Poly(Pt, x, y, t, *w, *U).coeffs()), 'integer coefficients')
xp, xn, yp, yn = s.symbols('xp xn yp yn')
Pnatural = Pt.subs({x:xp-xn, y:yp-yn}) + (xp*xn)**2 + (yp*yn)**2
require(s.Poly(Pnatural, xp, xn, yp, yn, t, *w, *U).total_degree() == 4, 'all-natural external degree')
require(len(w) == 2+2+2*2 and len(residuals(x,y,w)) == 1+2+2+2*2, 'membership counts')
require(len(w)+len(U) == 2+2+2*2+3 and len(timed_residuals(x,y,t,w,U)) == 2+2+2+2*2+3, 'timed counts')
COUNTS['symbolic_degree_count_checks'] = 6

# Exhaustive finite membership-witness cube, including inactive and negative quotients.
cube = tuple(product(range(3), repeat=8))
number = 0
for X, Y in product(range(-2,3), repeat=2):
    zeros = [v for v in cube if all(r == 0 for r in residuals(X,Y,v))]
    can = canonical(X,Y)
    want = [] if can is None or max(can[0]) > 2 else [can[0]]
    require(zeros == want, ('cube mismatch', X, Y, zeros, want))
    number += len(cube)
COUNTS['full_membership_cube_evaluations'] = number

# Larger signed-site fixtures and one-slot perturbations of every canonical witness.
canonical_cases = mutations = wrong_times = 0
for X, Y in product(range(-30,31), repeat=2):
    can = canonical(X,Y)
    if can is None:
        continue
    v, squares, T = can
    require(all(r == 0 for r in timed_residuals(X,Y,T,v,squares)), 'canonical timed residual')
    require(T >= 0, 'natural first-time fixture')
    canonical_cases += 1
    vector = (*v, *squares, T)
    for index in range(len(vector)):
        for delta in (-1, 1):
            mutated = list(vector)
            mutated[index] += delta
            if mutated[index] < 0:
                continue
            rs = timed_residuals(X,Y,mutated[-1],mutated[:8],mutated[8:11])
            require(any(r != 0 for r in rs), 'accepted altered witness')
            mutations += 1
    for wrong in (T-1, T+1):
        require(any(r != 0 for r in timed_residuals(X,Y,wrong,v,squares)), 'accepted wrong external time')
        wrong_times += 1
COUNTS['canonical_signed_site_cases'] = canonical_cases
COUNTS['rejected_one_slot_mutations'] = mutations
COUNTS['rejected_wrong_external_times'] = wrong_times

# Canonical quotient behavior independently covers both signs, zero, and inactive slots.
quotient_tests = 0
for Q in range(-10,11):
    pairs = [(a,b) for a,b in product(range(11), repeat=2) if a-b == Q and a*b == 0]
    require(pairs == [split(Q)], 'signed quotient uniqueness')
    quotient_tests += 121
COUNTS['quotient_pair_cube_evaluations'] = quotient_tests

# Check polarization and common denominator on all signed integer fixture points.
for X, Y in product(range(-10,11), repeat=2):
    a,b,c = X*X,Y*Y,(X+Y)**2
    require(Fraction(2*a+2,4) == Fraction(X*X+1,2), 'first branch denominator')
    require(Fraction(a+b+c+2*X,4) == Fraction(X*X+X*Y+Y*Y+X,2), 'mixed branch denominator')
COUNTS['polarization_and_denominator_cases'] = 441
# Application-specific shared-counter fixture, including an infinite prefix-hit domain.
# Branches: x=0 (time 2 for every y), x>0, x<0. Common clock c=1/2,b=3/2.
e0, ep, en, up, un, N = s.symbols('e0 ep en up un N')
def clock_residuals(X,T,v):
    e0,ep,en,up,un,N = v
    return (e0+ep+en-1, e0*X, ep*(X-1)-up, en*(-X-1)-un,
            N-ep*X+en*X,
            2*T-N*N-3*N-4*e0-2*ep*(X+5)-14*en)
clock_symbolic = clock_residuals(x,t,(e0,ep,en,up,un,N))
clock_poly = s.Poly(sum(r*r for r in clock_symbolic), x,t,e0,ep,en,up,un,N)
require(clock_poly.total_degree() == 4, 'shared-counter degree')
require(all(c.is_Integer for c in clock_poly.coeffs()), 'shared-counter integer coefficients')
require(len(clock_symbolic) == 3+2+1 and 6 == 3+2+1, 'shared-counter counts')
clock_cases = 0
clock_mutations = 0
for X in range(-30,31):
    if X == 0:
        v = (1,0,0,0,0,0)
        T = 2
    elif X > 0:
        v = (0,1,0,X-1,0,X)
        T = (X*X+3*X)//2+X+5
    else:
        v = (0,0,1,0,-X-1,-X)
        T = (X*X-3*X)//2+7
    require(all(r == 0 for r in clock_residuals(X,T,v)), 'shared-counter canonical value')
    clock_cases += 1
    for index in range(6):
        a=list(v)
        a[index] += 1
        require(any(r != 0 for r in clock_residuals(X,T,a)), 'shared-counter mutation accepted')
        clock_mutations += 1
    require(any(r != 0 for r in clock_residuals(X,T+1,v)), 'shared-counter wrong time accepted')
COUNTS['shared_counter_cases'] = clock_cases
COUNTS['shared_counter_rejected_mutations'] = clock_mutations
COUNTS['shared_counter_symbolic_checks'] = 3
COUNTS['limitations'] = 'Finite algebra fixtures only; no general CA normal-form or Presburger QE implementation.'
print(json.dumps(COUNTS, sort_keys=True, indent=2))
