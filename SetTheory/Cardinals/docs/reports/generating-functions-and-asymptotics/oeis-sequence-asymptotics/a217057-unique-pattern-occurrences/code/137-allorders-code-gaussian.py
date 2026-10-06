import sys
if not sys.flags.isolated:
    sys.stderr.write("REJECTED: isolated Python (-I) is required\n")
    raise SystemExit(2)
sys.dont_write_bytecode = True

"""Finite character/Gaussian algorithm; no optional explicit f_3 formula is used.

All coefficients are Fractions. For a chosen finite order, build Taylor
polynomials, multiply, then apply Wick's recurrence with covariance
[[1,-1/2],[-1/2,1]] and Vandermonde-squared weight. The analytic proof,
not this finite calculation, supplies uniform errors and all-order existence.
"""
from functools import lru_cache
from fractions import Fraction as F
from math import comb, factorial
from exact_algebra import (add, scale, multiply, power, constant, variable,
    series_log, series_exp, series_multiply, series_inverse, series_power,
    ordinary_series_inverse, ordinary_series_product, rational_strings, require)

X, Y = variable(0), variable(1)
D = [add(X, scale(Y, -1)), add(X, scale(Y, 2)), add(scale(X, 2), Y)]
DELTA2 = multiply(multiply(power(D[0], 2), power(D[1], 2)), power(D[2], 2))

@lru_cache(None)
def wick(a, b):
    if a < 0 or b < 0:
        return F()
    if a == 0:
        if b == 0:
            return F(1)
        return F() if b % 2 else (b-1) * wick(0, b-2)
    return (a-1) * wick(a-2, b) - F(b, 2) * wick(a-1, b-1)


def gaussian_raw(poly):
    return sum((coefficient * wick(*powers) for powers, coefficient in poly.items()), F())

NORMALIZATION = gaussian_raw(DELTA2)

@lru_cache(None)
def weighted_monomial(a, b):
    return sum((c * wick(p[0]+a, p[1]+b) for p, c in DELTA2.items()), F()) / NORMALIZATION


def expectation(poly):
    return sum((c * weighted_monomial(*p) for p, c in poly.items()), F())

@lru_cache(None)
def local_density(order):
    """Coefficient polynomials after removing exp(-Q/3) and m^-4."""
    require(type(order) is int and order >= 0, 'nonnegative integer order')
    trace = [constant(1)] + [scale(add(*(power(d, 2*h) for d in D)),
                  F(2*(-1)**h, 9*factorial(2*h))) for h in range(1, order+2)]
    logs = series_log(trace, order+1)
    # L_2 supplies the Gaussian; m L_{2h} contributes order m^{1-h}.
    phase = [{}] + logs[2:order+2]
    exponent = series_exp(phase, order)
    density = [constant(1)] + [{} for _ in range(order)]
    for d in D:
        factor = [scale(power(d, 2*h), F(2*(-1)**h, factorial(2*h+2)))
                  for h in range(order+1)]
        density = series_multiply(density, factor, order)
    return series_multiply(density, exponent, order)


def avoidance_coefficients(order):
    return [expectation(poly) for poly in local_density(order)]

@lru_cache(None)
def normalized_character(p, degree):
    """Taylor of h_p(e^{r theta})/[c_p (P(r theta)/3)^p], r formal."""
    require(type(p) is int and p >= 0, 'nonnegative boundary parameter')
    centered = [X, Y, scale(add(X, Y), -1)]
    z = [scale(add(*(power(theta, k) for theta in centered)), F(1, 3*factorial(k)))
         for k in range(degree+1)]
    g = [{} for _ in range(degree+1)]
    cp = comb(p+2, 2)
    for a in range(p+1):
        for b in range(p-a+1):
            c = p-a-b
            theta = add(scale(X, a-c), scale(Y, b-c))
            for k in range(degree+1):
                g[k] = add(g[k], scale(power(theta, k), F(1, cp*factorial(k))))
    reciprocal = series_power(series_inverse(z, degree), p, degree)
    return series_multiply(g, reciprocal, degree)

@lru_cache(None)
def boundary_coefficients(p, q, order):
    degree = 2*order
    left = normalized_character(p, degree)
    right = [scale(poly, (-1)**k) for k, poly in enumerate(normalized_character(q, degree))]
    product = series_multiply(left, right, degree)
    # r=i/sqrt(m): retain real even powers; imaginary odd parts integrate to zero.
    amplitude = [scale(product[2*h], (-1)**h) for h in range(order+1)]
    density = local_density(order)
    raw = [expectation(poly) for poly in series_multiply(density, amplitude, order)]
    return tuple(ordinary_series_product(raw, ordinary_series_inverse(avoidance_coefficients(order), order), order))


def d(p):
    return F(comb(p+2, 2), 3**p)


def half_coefficients(i, j, order):
    """Return U_h(i,j)/C_0, 0<=h<=order, by finite shifted character algebra."""
    alpha = avoidance_coefficients(order)
    def component(p, q, shift):
        raw = ordinary_series_product(alpha, boundary_coefficients(p, q, order), order)
        return [9**shift * d(p)*d(q) * sum((raw[h] * (-shift)**(n-h) *
                comb(3+n, n-h) for h in range(n+1)), F()) for n in range(order+1)]
    left = component(i+1, j+1, 2)
    right = component(i, j, 1)
    return [a-b for a, b in zip(left, right)]


def falling(n, degree):
    result = 1
    for k in range(degree):
        result *= n-k
    return result


def checks():
    alpha = avoidance_coefficients(3)
    require(NORMALIZATION == F(81, 2), 'Gaussian Vandermonde normalization')
    require(alpha == [1, F(-11, 2), 20, F(-965, 16)], 'avoidance alpha_0..alpha_3')
    moment_count = 0
    for p in range(13):
        compositions = [(a,b,p-a-b) for a in range(p+1) for b in range(p-a+1)]
        for a in range(7):
            for b in range(7-a):
                for c in range(7-a-b):
                    total = a+b+c
                    direct = F(sum(falling(x,a)*falling(y,b)*falling(z,c)
                                   for x,y,z in compositions), len(compositions))
                    closed = F(2*factorial(a)*factorial(b)*factorial(c)*falling(p,total), factorial(total+2))
                    require(direct == closed, 'weak composition moment identity')
                    moment_count += 1
    rows = {}
    for p,q in [(0,0),(0,1),(1,1),(2,0),(2,2),(2,3),(3,2),(4,0)]:
        f = boundary_coefficients(p,q,3)
        require(f[0] == 1, 'boundary leading coefficient')
        require(f[1] == -F(p*(p-1)+q*(q-1),2), 'boundary first correction')
        require(f == boundary_coefficients(q,p,3), 'boundary symmetry')
        if p in (0,1) and q in (0,1):
            require(f == (1,0,0,0), 'vacuous boundary')
        rows[f'{p},{q}'] = rational_strings(f)
    require(boundary_coefficients(2,0,3)[3] == F(11,16), 'boundary (2,0) third correction')
    halves = {}
    for i,j in [(0,0),(0,1),(1,0),(1,1),(2,0)]:
        values = half_coefficients(i,j,3)
        C = 81*d(i+1)*d(j+1)-9*d(i)*d(j)
        ai, aj = F(i*(i-1),2), F(j*(j-1),2)
        B = -81*d(i+1)*d(j+1)*(8+F(i*(i+1),2)+F(j*(j+1),2)) + 9*d(i)*d(j)*(4+ai+aj)
        require(values[0] == C and values[1] == -F(11,2)*C+B, 'half U_0,U_1')
        halves[f'{i},{j}'] = rational_strings(values)
    return {'normalization':str(NORMALIZATION), 'avoidance':rational_strings(alpha),
            'weak_composition_moment_checks':moment_count, 'boundary_samples':rows,
            'half_samples_divided_by_C0':halves,
            'scope':'Finite exact Gaussian and character algebra; no analytic error estimates or explicit symbolic f_3 formula are certified by this replay.'}
