#!/usr/bin/env python3
"""Exact consistency checks using only the Python standard library (Python 3.12)."""
from fractions import Fraction as F


def poly_add(left, right):
    keys = left.keys() | right.keys()
    return {k: total for k in keys if (total := left.get(k, 0) + right.get(k, 0))}


def poly_scale(poly, scalar):
    return {key: value*scalar for key, value in poly.items() if value*scalar}


def poly_mul(left, right):
    out = {}
    for (a, b), v in left.items():
        for (c, d), w in right.items():
            key = (a+c, b+d)
            out[key] = out.get(key, 0) + v*w
    return {key: value for key, value in out.items() if value}


def check_kernel():
    # Monomials are indexed by powers of (x,h). Clear pi and both denominators.
    x2 = {(2, 0): 1}
    h2 = {(0, 2): 1}
    two_h = {(0, 1): 2}
    denom_h = poly_add(x2, h2)
    denom_2h = poly_add(x2, poly_scale(h2, 4))
    cleared = poly_add(poly_mul(two_h, denom_2h),
                       poly_scale(poly_mul(two_h, denom_h), -1))
    assert cleared == {(0, 3): 6}
    print("PASS kernel: cleared numerator is 6 h^3 in Z[x,h].")


def mat_add(a, b):
    return tuple(tuple(x+y for x, y in zip(row, other)) for row, other in zip(a, b))


def mat_mul(a, b):
    return tuple(tuple(sum(x*y for x, y in zip(row, col)) for col in zip(*b)) for row in a)


def trace(a):
    return a[0][0] + a[1][1]


def check_coefficients(a, b, c, drift):
    # The trace-side coefficients come from a noncommutative power expansion.
    d = mat_add(a, ((drift, 0), (0, drift)))
    c2 = mat_mul(c, c)
    d2 = mat_mul(d, d)
    b2 = mat_mul(b, b)
    trace_coeffs = [
        trace(b),
        -trace(mat_mul(c, b)),
        trace(mat_mul(c2, b))-trace(mat_mul(d2, b))-trace(mat_mul(d, b2))
        -F(trace(mat_mul(b2, b)), 3)
    ]

    def gauss_add(x, y):
        return x[0]+y[0], x[1]+y[1]

    def gauss_mul(x, y):
        return x[0]*y[0]-x[1]*y[1], x[0]*y[1]+x[1]*y[0]

    def scale(z, s):
        return z[0]*s, z[1]*s

    def log_det_coeffs(m):
        # Calculate D(t)=det(I+t(C+i m)) from the four entries.
        entry = [[(c[i][j], m[i][j]) for j in range(2)] for i in range(2)]
        det = [(1, 0), gauss_add(entry[0][0], entry[1][1]),
               gauss_add(gauss_mul(entry[0][0], entry[1][1]),
                         scale(gauss_mul(entry[0][1], entry[1][0]), -1))]
        # Independently form the Taylor series of D'/D via series division,
        # then integrate it. No matrix-power or trace-log formula enters here.
        derivative = [det[1], scale(det[2], 2), (0, 0)]
        quotient = []
        for j, numerator in enumerate(derivative):
            current = numerator
            for k in range(1, min(j, 2)+1):
                current = gauss_add(current, scale(gauss_mul(det[k], quotient[j-k]), -1))
            quotient.append(current)
        return [F(q[1], j+1) for j, q in enumerate(quotient)]

    after, before = log_det_coeffs(mat_add(d, b)), log_det_coeffs(d)
    assert mat_mul(a, b) != mat_mul(b, a)
    assert mat_mul(c, a) != mat_mul(a, c)
    assert trace_coeffs == [x-y for x, y in zip(after, before)]
    return ", ".join(str(x) for x in trace_coeffs)


def main():
    check_kernel()
    a = ((2, 1), (1, -1))
    c = ((F(1, 3), 0), (0, F(-2, 5)))
    drift = F(-3, 4)  # rational surrogate for the real displacement -pi/4
    for name, b in (("rank one", ((1, 1), (1, 1))),
                    ("full rank", ((2, -1), (-1, 3)))):
        coeffs = check_coefficients(a, b, c, drift)
        print(f"PASS {name}: imaginary coefficients at orders 1, 2, 3 = {coeffs}.")


if __name__ == "__main__":
    main()
