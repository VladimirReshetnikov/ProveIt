#!/usr/bin/env python3
"""Independent, exact, standard-library check of the two counterexamples."""
from math import comb


def check(condition, message):
    if not condition:
        raise AssertionError(message)


def split(coefficients):
    g, h = [1], []
    for k, value in enumerate(coefficients[1:], 1):
        r, kap = 0, 0
        for lower in range(k, 0, -1):
            if value == 0:
                break
            upper = lower
            while comb(upper + 1, lower) <= value:
                upper += 1
            value -= comb(upper, lower)
            r += comb(upper - 1, lower)
            kap += comb(upper - 1, lower - 1)
        check(value == 0, "unrepresented remainder")
        g.append(r)
        h.append(kap)
    return g, h


def D(a, b, c):
    return a*a*b*b - 4*b*b*b - 4*a*a*a*c - 27*c*c + 18*a*b*c


def product(slopes):
    coefficients = [1]
    for a in slopes:
        updated = [0] * (len(coefficients) + 1)
        for i, coefficient in enumerate(coefficients):
            updated[i] += coefficient
            updated[i + 1] += a * coefficient
        coefficients = updated
    return coefficients


for slopes, expected_f, expected_g, expected_h, dg, dh in [
    ((2, 3, 3), [1, 8, 21, 18], [1, 7, 15, 8], [1, 6, 10], -59, -4),
    ((2, 3, 4), [1, 9, 26, 24], [1, 8, 19, 11], [1, 7, 13], -31, -3),
]:
    f = product(slopes)
    check(f == expected_f, "factor expansion disagrees")
    g, h = split(f)
    check(g == expected_g and h == expected_h, "canonical split disagrees")
    check(all(f[k] == g[k] + h[k-1] for k in range(1, 4)), "F != G+tH")
    check(D(*g[1:]) == dg < 0, "G discriminant is not as claimed")
    check(h[1]**2 - 4*h[2] == dh < 0, "H discriminant is not as claimed")
    print(f"slopes={slopes}: F={f}, G={g}, H={h}, disc(G)={dg}, disc(H)={dh}")
print("BOTH EXACT COUNTEREXAMPLE CERTIFICATES PASSED")
