#!/usr/bin/env python3
"""Exact algebraic regression checks for the exponent-five manuscript.

Requires Python 3 and SymPy. All arithmetic is exact. These checks validate
identities and finite residue tables, plus a bounded sample of the explicit
Euclidean and normalization algorithms. They do NOT prove FLT, termination
of the general descent, or derivability in iPRA.
"""
from fractions import Fraction
from itertools import product
import sympy as sp

CHECKS = 0


def check(condition, label):
    global CHECKS
    if not condition:
        raise AssertionError(label)
    CHECKS += 1


def identity(lhs, rhs, label):
    check(sp.expand(lhs - rhs) == 0, label)


def add(x, y):
    return x[0] + y[0], x[1] + y[1]


def neg(x):
    return -x[0], -x[1]


def sub(x, y):
    return add(x, neg(y))


def mul(x, y):
    a, b = x
    c, d = y
    return a*c + b*d, a*d + b*c + b*d


def conj(x):
    a, b = x
    return a+b, -b


def norm(x):
    a, b = x
    return a*a + a*b - b*b


def power(x, k):
    assert k >= 0
    ans = (1, 0)
    for _ in range(k):
        ans = mul(ans, x)
    return ans


def phi_power(k):
    return power((0, 1) if k >= 0 else (-1, 1), abs(k))


def F(t, s):
    return t**4 + 10*t*t*s*s + 5*s**4


def G(t, s):
    return t**4 + 50*t*t*s*s + 125*s**4


def sign_int(n):
    return (n > 0) - (n < 0)


def sign_phi(x):
    """Exact sign of a+b*phi via (2a+b)+b*sqrt(5)."""
    a, b = x
    A, B = 2*a+b, b
    if B == 0:
        return sign_int(A)
    if A == 0:
        return sign_int(B)
    if A > 0 and B > 0:
        return 1
    if A < 0 and B < 0:
        return -1
    if A > 0:  # B < 0
        return sign_int(A*A - 5*B*B)
    return sign_int(5*B*B - A*A)


def nearest(r):
    """Nearest integer, with half-integer ties towards positive infinity."""
    r = Fraction(r)
    return (2*r.numerator+r.denominator) // (2*r.denominator)


def euclidean_step(alpha, beta):
    assert beta != (0, 0)
    D = norm(beta)
    assert D != 0
    numerator = mul(alpha, conj(beta))
    q = tuple(nearest(Fraction(v, D)) for v in numerator)
    rem = sub(alpha, mul(q, beta))
    return q, rem


def normalize(alpha):
    """Return signed exponent k and associate in [1,phi), bounded scan."""
    assert alpha != (0, 0)
    H = abs(alpha[0]) + abs(alpha[1]) + 1
    signed = alpha if sign_phi(alpha) > 0 else neg(alpha)
    for k in range(-4*H, 4*H+1):
        v = mul(signed, phi_power(k))
        if sign_phi(sub(v, (1, 0))) >= 0:
            assert sign_phi(sub(v, (0, 1))) < 0
            return k, v
    raise AssertionError("bounded normalization scan failed")


def symbolic_checks():
    a, b, c, d = sp.symbols("a b c d", integer=True)
    alpha, beta = (a, b), (c, d)
    identity(norm(mul(alpha, beta)), norm(alpha)*norm(beta),
             "golden norm multiplicativity")
    alpha_bar = mul(alpha, conj(alpha))
    identity(alpha_bar[0], norm(alpha), "alpha conjugate real coordinate")
    identity(alpha_bar[1], 0, "alpha conjugate phi coordinate")
    identity(norm(conj(alpha)), norm(alpha), "conjugate norm")

    t, s, p, q, r, x, y, k, J = sp.symbols(
        "t s p q r x y k J", integer=True)
    # t+s*sqrt(5) = (t-s)+2s*phi.
    direct = power((t-s, 2*s), 5)
    identity(direct[1]/2, 5*s*F(t, s), "direct fifth sqrt coefficient")
    identity(direct[0]+direct[1]/2, t*G(t, s),
             "direct fifth rational coefficient")
    # (t+s*sqrt(5))/2 = (t-s)/2+s*phi.
    half = power(((t-s)/2, s), 5)
    identity(16*half[1], 5*s*F(t, s), "half fifth sqrt numerator")
    identity(16*(2*half[0]+half[1]), t*G(t, s),
             "half fifth rational numerator")
    identity((t*t+5*s*s)**2 - 5*(2*s*s)**2, F(t, s),
             "iterated norm identity")
    identity((q*q+25*r*r)**2 - 5*(10*r*r)**2, G(q, r),
             "initial norm identity")
    identity((x+y)*F(x+y, x-y), 16*(x**5+y**5),
             "opposite parity entry identity")
    identity(2*p*F(p, q), (p+q)**5+(p-q)**5,
             "both odd entry identity")
    identity((5*r)*F(5*r, q), 25*r*G(q, r),
             "substitution p=5r")
    identity(625*(16*r*r), 16*(25*r)**2, "initial odd h=4")
    identity(2*625*(2*r*r), (50*r)**2, "initial even h=4")
    identity((5*k*k*J).subs(J, sp.Rational(16, 5)*s*s),
             16*(k*s)**2, "odd h to 2h+1 transition")
    identity((2*5*k*k*J).subs(J, sp.Rational(2, 5)*s*s),
             (2*k*s)**2, "even h to 2h+1 transition")

    P = (q*q+25*r*r)/2
    Q = 5*r*r
    identity(P*P-5*Q*Q, G(q, r)/4, "initial half norm")
    P = (t*t+5*s*s)/2
    Q = s*s
    identity(P*P-5*Q*Q, F(t, s)/4, "iterated half norm")


def residue_checks():
    phi_table = [(1, 0), (0, 1), (1, 1), (1, 2), (2, 3)]
    for r, pair in enumerate(phi_table):
        check(power((0, 1), r) == pair, "phi remainder table")
    for a, b in product(range(5), repeat=2):
        fifth = power((a, b), 5)
        check(tuple(v % 5 for v in fifth) == ((a+3*b) % 5, 0),
              "fifth power scalar modulo five")
    for r, scalar in product(range(5), range(1, 5)):
        A, B = (scalar*v % 5 for v in phi_table[r])
        check(not (B == 0 and A != 0) or r == 0,
              "unit ambiguity modulo five")
    for a, b in product(range(2), repeat=2):
        fourth = power((a, b), 4)
        fifth = power((a, b), 5)
        check(tuple(v % 2 for v in fourth) == (a, b),
              "fourth Frobenius modulo two")
        check(fifth[1] % 2 == b, "fifth phi coordinate parity")
    residue_set = {pow(a, 5, 25) for a in range(25)}
    units = {pow(a, 5, 25) for a in range(25) if a % 5}
    check(residue_set == {0, 1, 7, 18, 24}, "fifth residues modulo 25")
    check(units == {1, 7, 18, 24}, "unit fifth residues modulo 25")
    for a, b, c in product(units, repeat=3):
        check((a+b+c) % 25 != 0, "modulo-25 first-case obstruction")
    for t, s in product(range(1, 16, 2), repeat=2):
        check(F(t, s) % 16 == 0, "F odd-odd divisible by sixteen")
        check(G(t, s) % 16 == 0, "G odd-odd divisible by sixteen")
    for t in range(1, 16, 2):
        for s in range(0, 16, 2):
            check(F(t, s) % 2 == 1, "F odd-even odd")
            check(G(t, s) % 2 == 1, "G odd-even odd")


def bounded_algorithm_samples():
    pairs = list(product(range(-3, 4), repeat=2))
    for alpha in pairs:
        for beta in pairs:
            if beta == (0, 0):
                continue
            q, rem = euclidean_step(alpha, beta)
            check(add(mul(q, beta), rem) == alpha, "division identity sample")
            check(4*abs(norm(rem)) <= 3*abs(norm(beta)),
                  "three-quarters norm remainder sample")
            check(abs(norm(rem)) < abs(norm(beta)),
                  "strict norm decrease sample")
    for alpha in product(range(-6, 7), repeat=2):
        if alpha == (0, 0):
            continue
        H = abs(alpha[0])+abs(alpha[1])+1
        k, v = normalize(alpha)
        check(abs(k) <= 4*H, "bounded unit exponent sample")
        check(abs(norm(v)) == abs(norm(alpha)), "associate norm sample")
        check(max(abs(v[0]), abs(v[1])) <= 3*abs(norm(alpha))+6,
              "normalized coordinate box sample")
        if abs(norm(alpha)) == 1:
            check(v == (1, 0), "normalized unit sample")


if __name__ == "__main__":
    print("Exact exponent-five algebra checks (not a proof of FLT or iPRA derivability).")
    symbolic_checks()
    residue_checks()
    bounded_algorithm_samples()
    print(f"PASS: {CHECKS} exact identities, residue cases, and bounded algorithm samples.")
    print("The manuscript supplies the mathematical descent and the uniform boundedness arguments.")

