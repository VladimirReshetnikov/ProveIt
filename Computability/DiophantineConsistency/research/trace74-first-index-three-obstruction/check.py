#!/usr/bin/env python3
"""Exact sparse-polynomial certificates; no Lean or graph-zero evaluation."""
import json
import sys

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')

# Three formal integer variables; coefficients and exponents are exact.
Z = (0, 0, 0)
def const(n): return {} if n == 0 else {Z: n}
def add(a, b):
    r = dict(a)
    for k, v in b.items():
        r[k] = r.get(k, 0) + v
        if r[k] == 0: del r[k]
    return r
def neg(a): return {k: -v for k, v in a.items()}
def sub(a, b): return add(a, neg(b))
def scale(n, a): return {k: n*v for k, v in a.items() if n*v}
def mul(a, b):
    r = {}
    for ka, va in a.items():
        for kb, vb in b.items():
            k = tuple(x+y for x, y in zip(ka, kb))
            r[k] = r.get(k, 0) + va*vb
    return {k: v for k, v in r.items() if v}
def power(a, n):
    r = const(1)
    for _ in range(n): r = mul(r, a)
    return r
def plus(*terms):
    r = {}
    for a in terms: r = add(r, a)
    return r
def var(i): return {tuple(int(j == i) for j in range(3)): 1}
def evaluate(a, values):
    return sum(v*values[0]**k[0]*values[1]**k[1]*values[2]**k[2] for k, v in a.items())
def substitute(a, replacements):
    r = {}
    for exponents, coefficient in a.items():
        term = const(coefficient)
        for replacement, exponent in zip(replacements, exponents):
            term = mul(term, power(replacement, exponent))
        r = add(r, term)
    return r

one = const(1)
X, Y, W = (var(i) for i in range(3))
A = add(X, one)
P = mul(X, power(Y, 2))
k = plus(scale(32, power(P, 2)), scale(32, P), const(6))
t = add(mul(A, Y), one)
c = plus(scale(16, power(t, 4)), scale(-12, power(t, 2)), one)
D = sub(power(A, 4), scale(2, mul(power(X, 2), Y)))

# Derive the two Pell y-polynomials directly from the universal recurrence
# x_{m+1}=t*x_m+(t²−1)*y_m, y_{m+1}=x_m+t*y_m.
T = var(2)
xp, yp = one, {}
ordinates = {}
for n in range(1, 6):
    xp, yp = add(mul(T, xp), mul(sub(power(T, 2), one), yp)), add(xp, mul(T, yp))
    ordinates[n] = yp
assert ordinates[3] == sub(scale(4, power(T, 2)), one)
assert ordinates[5] == plus(scale(16, power(T, 4)), scale(-12, power(T, 2)), one)
first_t = add(scale(2, P), one)
assert k == scale(2, sub(scale(4, power(first_t, 2)), one))
assert c == plus(scale(16, power(t, 4)), scale(-12, power(t, 2)), one)

lhs = sub(c, mul(k, Y))
rhs = plus(scale(16, mul(power(Y, 4), D)),
           mul(sub(scale(64, power(A, 3)), scale(32, X)), power(Y, 3)),
           scale(84, mul(power(A, 2), power(Y, 2))),
           mul(sub(scale(40, A), const(6)), Y), const(5))
assert lhs == rhs

# W is the nonnegative slack X²+4X+4−2Y. This identity is valid without
# assuming that equation; it displays precisely its residual.
lower = plus(scale(16, mul(power(Y, 4), plus(mul(power(X, 2), W), scale(4, X), one))),
             scale(32, mul(plus(scale(2, power(X, 3)), scale(6, power(X, 2)), scale(5, X), const(2)), power(Y, 3))),
             mul(plus(scale(84, power(X, 2)), scale(136, X), const(84)), power(Y, 2)),
             scale(40, mul(X, Y)), scale(34, sub(Y, one)), const(33))
constraint = sub(plus(power(X, 2), scale(4, X), const(4)), plus(scale(2, Y), W))
assert sub(sub(c, mul(k, add(Y, one))), lower) == scale(16, mul(mul(power(X, 2), power(Y, 4)), constraint))

# If 2Y=X²+4X+8+W and X=32+U, kY−c is a polynomial with
# strictly positive coefficients in U,W.  The third variable is unused.
U, W2 = var(0), var(1)
xx = add(const(32), U)
tt = plus(power(xx, 2), scale(4, xx), const(8), W2)
z = plus(mul(add(xx, one), tt), const(2))
upper = plus(mul(power(xx, 2), power(tt, 5)), scale(4, mul(xx, power(tt, 3))),
             scale(3, tt), neg(power(z, 4)), scale(3, power(z, 2)), const(-1))
assert len(upper) == 46
assert all(value > 0 and exp[2] == 0 for exp, value in upper.items())

# The denominator-free expression is an exact polynomial identity at t=2Y.
two_y = scale(2, Y)
z0 = plus(mul(add(X, one), two_y), const(2))
upper_raw = plus(mul(power(X, 2), power(two_y, 5)), scale(4, mul(X, power(two_y, 3))),
                 scale(3, two_y), neg(power(z0, 4)), scale(3, power(z0, 2)), const(-1))
assert upper_raw == sub(mul(k, Y), c)
formal_t = var(1)
formal_z = plus(mul(add(X, one), formal_t), const(2))
formal_upper = plus(mul(power(X, 2), power(formal_t, 5)), scale(4, mul(X, power(formal_t, 3))),
                    scale(3, formal_t), neg(power(formal_z, 4)), scale(3, power(formal_z, 2)), const(-1))
assert substitute(formal_upper, (xx, tt, {})) == upper

# X=q*w and Y=q³*s force q | (2Y−X²−4X), with q,w,s formal.
q, w, s = (var(i) for i in range(3))
xxq, yyq = mul(q, w), mul(power(q, 3), s)
residue = sub(sub(scale(2, yyq), power(xxq, 2)), scale(4, xxq))
factor = sub(sub(scale(2, mul(power(q, 2), s)), mul(q, power(w, 2))), scale(4, w))
assert residue == mul(q, factor)

# Independently cross-check the substitution polynomial on exact integers.
for xx0 in (32, 33, 64, 127):
    for w0 in (0, 1, 7):
        tt0 = xx0*xx0+4*xx0+8+w0
        if tt0 % 2: continue
        yy0 = tt0//2
        assert evaluate(upper, (xx0-32, w0, 0)) == evaluate(sub(mul(k, Y), c), (xx0, yy0, 0))

print(json.dumps({'status':'PASS','recurrence_y3_y5':True,
 'corrected_difference_identity':True,'lower_slack_identity':True,
 'upper_substitution_identity':True,'q_divisibility_identity':True,
 'upper_positive_coefficient_terms':len(upper),'upper_min_coefficient':min(upper.values()),
 'upper_constant_coefficient':upper.get(Z,0),
 'scope':'integer polynomial certificates; conditional scalar obstruction only; no Lean, graph-zero or fixed-port theorem'},sort_keys=True))
