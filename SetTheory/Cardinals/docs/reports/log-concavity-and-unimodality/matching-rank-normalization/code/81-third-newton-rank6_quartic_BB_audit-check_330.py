#!/usr/bin/env python3
"""Exact independent Schur and endpoint identities for BB (3,3,0)."""
from itertools import combinations, permutations
from pathlib import Path
import json
import sympy as s

p, m, q, h, z = s.symbols('p m q h z')
t, u, Z, y = s.symbols('t u Z y')


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def equal(left, right, label):
    require(s.cancel(left - right) == 0, label)


def matched(columns, slots):
    return any(all(mask & (1 << coordinate) for mask, coordinate in zip(columns, perm))
               for perm in permutations(slots))


def pairs(S, T):
    return sum(matched((S, T), I) for I in combinations(range(3), 2))


def triple(S, T, U):
    return int(matched((S, T, U), (0, 1, 2)))


E = p + 2 * m + 1
x = q + 2 * h + z
D = 2 * m ** 2 + 2 * m * p + p ** 2 - 3 * p
r = s.Matrix([p * S.bit_count() + m * pairs(3, S) + triple(3, 3, S)
              for S in range(1, 8)])
v = s.Matrix([q * S.bit_count() + h * pairs(3, S) + z * int(bool(S & 4))
              for S in range(1, 8)])
B = s.Matrix(7, 7, lambda i, j: p * pairs(i + 1, j + 1)
             + m * triple(3, i + 1, j + 1))
M = 3 * r * r.T / (4 * E) - B
w = 3 * x * r / (4 * E) - v
Y1 = (-2*h*m*p + 2*m**2*q - 2*m*p*q - p**2*q + 2*p**2*z - 3*p*q)/(p*D)
Y3 = (2*h*m*p + h*p**2 - 3*h*p - 4*m**2*q - 2*m*p*q + 2*m*p*z)/(p*D)
Y4 = (-h*m - 2*m*q - p*q + p*z)/D
Y = s.Matrix([Y1, Y1, Y3, Y4, 0, 0, 0])
for i in range(7):
    equal((M * Y)[i], w[i], ('inverse-cross-column', i))
equal(M.det(), p**4 * m * D / 4, 'R determinant')
N = p*(2*m+p-3)*h**2 + 4*p*(m+p-3)*h*q + 4*p*(2*m+p)*q*z \
    + 4*m*p*h*z - 2*p**2*z**2 - 2*(2*m**2+2*m*p+3*p)*q**2
equal(3*x*x/(4*E) - (w.T*Y)[0], N/(p*D), 'Schur numerator')
F = (2*m+p-3)*t*t + 4*(m+p-3)*t*u + 4*(2*m+p)*u + 4*m*t - 2*p \
    - 2*(2*m*m+2*m*p+3*p)*u*u/p
equal(N.subs({h:z*t, q:z*u})/(p*D), z*z*F/D, 'normalized quadratic')
G = (4*m*t-6*t*t)*p*p \
    + (m*m*t*t+8*m*m*t-2*m*m-12*m*t*t)*p \
    + 2*m**3*t*t+4*m**3*t-3*m*m*t*t
equal(m*m*F.subs(u,p*t/m), G, 'Rayleigh endpoint')
B0 = (m-12)*t*t+8*m*t-2*m
equal(B0.subs(t,(m-1)/2), (m**3+2*m*m+m-12)/4, 'lower t endpoint')
equal(B0.subs(t,m-1), m**3-6*m*m+15*m-12, 'upper t endpoint')
R = 2*Z**4+8*Z**3*y+13*Z**3+10*Z**2*y*y+45*Z**2*y+22*Z**2 \
    +4*Z*y**3+44*Z*y*y+72*Z*y+8*Z+12*y**3+48*y*y+24*y
endpoint = s.cancel(G.subs(p,m*(m-1)/2)/m**2)
equal(endpoint.subs(t,m-(z+1)/2).subs(m,z+y).subs(z,Z+1), R/8,
      'upper p endpoint polynomial')
require(all(c > 0 for c in s.Poly(R,Z,y).coeffs()), 'R positive coefficients')
equal((m**3-6*m*m+15*m-12).subs(m,y+2), y**3+3*y+2,
      'upper t endpoint positivity')
equal((m**3+2*m*m+m-12).subs(m,y+2), y**3+8*y*y+21*y+6,
      'lower t endpoint positivity')
out = {'status':'pass','profile':[3,3,0], 'R_determinant':str(p**4*m*D/4),
       'Schur_numerator':str(N),'Schur_denominator':str(p*D),
       'normalized_F':str(F),'Rayleigh_endpoint_G':str(G),
       'positive_endpoint_polynomial':str(R),
       'positive_endpoint_terms':len(s.Poly(R,Z,y).terms()),
       'source_N4_removed':True,'N4_restoration':'BB monotonicity lemma'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
