#!/usr/bin/env python3
"""Exact certificates for the spectrum {1,4,7}. Requires Python 3 and SymPy."""
from fractions import Fraction
from itertools import permutations
from math import factorial
import sympy as sp


class Interval:
    """Closed rational intervals with outward-exact arithmetic."""
    def __init__(self, lo, hi=None):
        if isinstance(lo, Interval):
            self.lo, self.hi = lo.lo, lo.hi
        else:
            self.lo = Fraction(lo)
            self.hi = self.lo if hi is None else Fraction(hi)
        assert self.lo <= self.hi

    def __add__(self, other):
        other = Interval(other)
        return Interval(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-Interval(other))

    def __rsub__(self, other):
        return Interval(other) + (-self)

    def __mul__(self, other):
        other = Interval(other)
        corners = [x * y for x in (self.lo, self.hi)
                   for y in (other.lo, other.hi)]
        return Interval(min(corners), max(corners))

    __rmul__ = __mul__


def evaluate(coefficients, x):
    ans = Interval(0)
    for c in coefficients:
        ans = ans * x + c
    return ans


def rational_coeffs(poly):
    return [Fraction(int(c.p), int(c.q)) for c in poly.all_coeffs()]


def evaluate_poly(poly, x):
    return evaluate(rational_coeffs(poly), x)


def band(value, radius='0.000000000000000001'):
    value, radius = Fraction(value), Fraction(radius)
    return Interval(value - radius, value + radius)


def det3(matrix):
    total = Interval(0)
    for i, j, k in permutations(range(3)):
        sign = 1 if (j - i) % 3 == 1 else -1
        total += sign * matrix[0][i] * matrix[1][j] * matrix[2][k]
    return total


s, x = sp.symbols('s x')
h = sp.Poly.from_list([165888, -912384, 1974528, -2154240, 1297800,
                       -467124, 105672, -15092, 1274, -49], x)
H = sp.Poly(h.as_expr().subs(x, s**2), s, domain=sp.QQ)
p_polynomial = sp.Poly.from_list([-5579891712, 30121984512, -63425084544,
                                  66376108800, -37602505764, 12510048822,
                                  -2542346352, 303526195, -18986709], x)
p = p_polynomial.as_expr().subs(x, s**2) / 3924844


def reduce_mod(expression):
    return sp.Poly(expression, s, domain=sp.QQ).rem(H).as_expr()


r = reduce_mod(3*s**2 - 2*p - sp.Rational(7, 4))
e = reduce_mod((-2*s*r + 2*s**3 + 2*s*p) * sp.invert(8*p**2 - 1, H.as_expr(), s))
q = x**2 - s*x + p
C = x**3 + 2*s*x**2 + r*x + e
F = sp.Poly(64*q**2*C, x)
B = reduce_mod(F.nth(0))
A = reduce_mod(F.nth(1) + 7)
T4, T7 = sp.chebyshevt(4, x), sp.chebyshevt(7, x)
resid = F - sp.Poly(A*x + B*T4 + T7, x)
assert all(reduce_mod(c) == 0 for c in resid.all_coeffs())

ss = band('1.12268200790234930920398351613290735', '0.00000000000000000000000000000000001')
assert H.eval(ss.lo)*H.eval(ss.hi) < 0
assert H.count_roots(ss.lo, ss.hi) == 1
pp, rr, ee = [evaluate_poly(sp.Poly(f, s), ss) for f in (p,r,e)]
ell = band('-0.3639080166421498774')
u = band('0.2680823592349304298')
v = band('0.8545996486674188794')
for z in (u, v):
    left = evaluate([1, -ss, pp], Interval(z.lo))
    right = evaluate([1, -ss, pp], Interval(z.hi))
    assert (left * right).hi < 0
assert evaluate([1, 2*ss, rr, ee], Interval(ell.lo)).hi < 0
assert evaluate([1, 2*ss, rr, ee], Interval(ell.hi)).lo > 0
# C'' > 0 to the right of ell.lo, and C'(ell.lo) > 0.
assert (6*ell.lo + 4*ss).lo > 0
assert evaluate([3, 4*ss, rr], Interval(ell.lo)).lo > 0
nodes = [ell, u, v]
xs = nodes
ys = [evaluate_poly(sp.Poly(T4, x), z) for z in nodes]
minors = [xs[(i+1)%3]*ys[(i+2)%3] - xs[(i+2)%3]*ys[(i+1)%3] for i in range(3)]
assert all(m.hi < 0 for m in minors)
sine_quotients = [[evaluate_poly(sp.Poly(sp.chebyshevu(n-1, x),x), z)
                   for z in nodes] for n in (1, 4, 7)]
assert det3(sine_quotients).lo > 0

# Validate the stated gap enclosure by the Taylor bound for cos.
pi = Interval('3.14159265358979323846264338327950288',
              '3.14159265358979323846264338327950289')
def atan_inv(k):
    # Alternating arctan series and its next term.
    v = sum(Fraction((-1)**i, (2*i+1)*k**(2*i+1)) for i in range(31))
    return Interval(v-Fraction(1,63*k**63), v)
machin = 16*atan_inv(5) - 4*atan_inv(239)
assert pi.lo < machin.lo < machin.hi < pi.hi
def cosine_pi(t):
    z = t*pi
    value = evaluate([Fraction((-1)**i,factorial(2*i)) for i in range(18,-1,-1)], z*z)
    error = Fraction(2**37,factorial(37))  # |pi*t| < 2
    assert 0 < z.lo < z.hi < 2
    return value + Interval(-error,error)
assert cosine_pi(Fraction('0.61855775348402062')).lo > ell.hi
assert cosine_pi(Fraction('0.61855775348402063')).hi < ell.lo

# The primitive integer resultant for y = 2*ell.
y = sp.Symbol('y')
R = sp.Poly(sp.resultant(H.as_expr(), C.subs(x,y/2), s), y)
Q = R.clear_denoms(convert=True)[1].primitive()[1]
if Q.LC() < 0:
    Q = -Q
assert Q.degree() == 54 and Q.LC() == 729
# Rabin irreducibility over F_211. The prime factors of 54 are 2 and 3.
qmod = sp.Poly(Q, y, modulus=211).monic()
Y = sp.Poly(y,y,modulus=211)
def power_mod(base, n, modulus):
    result = base.one
    while n:
        if n % 2:
            result = (result*base).rem(modulus)
        base = (base*base).rem(modulus)
        n //= 2
    return result

frobenius = Y
for i in range(1,55):
    frobenius = power_mod(frobenius,211,qmod)
    if i in (18,27):
        assert sp.gcd(frobenius-Y, qmod).degree() == 0
assert frobenius == Y
print('PASS: sparse factorization, isolating intervals, contact signs and unique positive rule.')
print('PASS: 0.61855775348402062 < M < 0.61855775348402063.')
print('PASS: 2*cos(pi*M) has degree 54, primitive leading coefficient 729, irreducible mod 211.')
print('Coefficients of the primitive polynomial, from degree 54 down to 0:')
print(Q.all_coeffs())
