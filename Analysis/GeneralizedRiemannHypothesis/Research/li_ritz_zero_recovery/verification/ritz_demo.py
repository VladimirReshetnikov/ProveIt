#!/usr/bin/env python3
"""Estimate positive zeta zero ordinates using completed-zeta Taylor data.

Requires Python 3 and mpmath 1.3.0. Run python ritz_demo.py. No zeta zero
ordinates enter the estimator. mpmath.zetazero is used only for comparison.
The cross-resolution check tests numerical stability; outputs are not intervals.
"""
import argparse
from mpmath import mp


SCALE = 200


def completed_zeta(u):
    """Return 2 xi(s) at u = s(1-s). Symmetry makes the square-root choice immaterial."""
    s = mp.mpf("0.5") + mp.sqrt(mp.mpf("0.25") - u)
    return s * (s - 1) * mp.power(mp.pi, -s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def power_sums(degree, points):
    """Cauchy quadrature followed by Newton sums, for the atoms 200/(1/4+gamma^2)."""
    radius = mp.mpf(32)
    # Paired conjugate samples halve the number of zeta evaluations.
    samples = []
    for k in range(points // 2 + 1):
        angle = 2 * mp.pi * k / points
        weight = 1 if k in (0, points // 2) else 2
        samples.append((angle, weight, completed_zeta(radius * mp.expj(angle))))
    coefficients = [mp.mpf(1)]
    for n in range(1, degree + 1):
        total = mp.fsum(w * mp.re(value * mp.expj(-n * t)) for t, w, value in samples)
        coefficients.append(total / points * (SCALE / radius) ** n)
    moments = [mp.mpf(0)]  # Zeroth power sum diverges and is never used.
    for n in range(1, degree + 1):
        cross_terms = mp.fsum(coefficients[n - k] * moments[k] for k in range(1, n))
        moments.append(-n * coefficients[n] - cross_terms)
    return moments


def estimates(moments, dimension):
    """Return upper ordinate estimates and any moment/residual lower bounds."""
    extended = mp.matrix(dimension + 1, dimension + 1)
    for i in range(dimension + 1):
        for j in range(dimension + 1):
            extended[i, j] = moments[1 + i + j]
    gram = extended[:dimension, :dimension]
    shifted = extended[:dimension, 1:]
    inverse = mp.inverse(mp.cholesky(gram))
    reduced = inverse * shifted * inverse.T
    eigenvalues, vectors = mp.eigsy((reduced + reduced.T) / 2)
    # The squared norm of the monic orthogonal polynomial of degree dimension.
    monic_norm = mp.cholesky(extended)[dimension, dimension] ** 2
    roots = list(reversed(list(eigenvalues)))
    rows = []
    for j, root in enumerate(roots):
        upper = mp.sqrt(SCALE / root - mp.mpf("0.25"))
        # eigenvectors of the moment pencil in ascending powers of the scaled x.
        polynomial = inverse.T * vectors[:, dimension - 1 - j]
        residual_squared = polynomial[dimension - 1] ** 2 * monic_norm
        candidates = []
        for k in range(1, 2 * dimension + 1):
            remainder = moments[k] - mp.fsum(y ** k for y in roots[:j])
            candidates.append(mp.root(remainder / 2, k))
        separator = min(candidates)
        lower = None
        if separator < root:
            outer = root + residual_squared / (root - separator)
            lower = mp.sqrt(max(mp.mpf(0), SCALE / outer - mp.mpf("0.25")))
        rows.append((upper, lower))
    return rows


def run(maximum, digits, points):
    with mp.workdps(digits):
        moments = power_sums(2 * maximum + 1, points)
        # The first moment has an independent closed form from xi'(1)/xi(1).
        first = 1 + mp.euler / 2 - mp.log(4 * mp.pi) / 2
        if abs(moments[1] / SCALE - first) > mp.mpf("1e-30"):
            raise ArithmeticError("First moment fails closed-form check")
        return [estimates(moments, n) for n in range(1, maximum + 1)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-dimension", type=int, choices=range(1, 9), default=8)
    args = parser.parse_args()
    maximum = args.max_dimension
    mp.dps = 100
    coarse = run(maximum, digits=85, points=80)
    fine = run(maximum, digits=100, points=104)
    difference = max(abs(x - y) for a, b in zip(coarse, fine) for r, s in zip(a, b)
                     for x, y in zip(r, s) if x is not None and y is not None)
    if difference > mp.mpf("1e-20"):
        raise ArithmeticError("Enlarging the quadrature changed a reported estimate")
    references = [mp.im(mp.zetazero(i)) for i in range(1, maximum + 1)]
    for n, row in enumerate(fine):
        for j, (value, lower) in enumerate(row):
            if not value >= references[j]:
                raise ArithmeticError("Unexpected direction of an ordinate bound")
            if lower is not None and lower > references[j]:
                raise ArithmeticError("Unexpected direction of the residual bound")
            if n and j < n and value > fine[n - 1][j][0]:
                raise ArithmeticError("Unexpected failure of interlacing")
    print("Estimated positive ordinates using moment pencils")
    print("N    first               second              third")
    for n, row in enumerate(fine, start=1):
        print(f"{n:<4} " + "  ".join(f"{mp.nstr(x, 15):<18}" for x, _ in row[:3]))
    print("ref  " + "  ".join(f"{mp.nstr(x, 15):<18}" for x in references[:3]))
    print(f"Two-sided ordinate bounds at N={maximum} (floating-point illustrations)")
    for j, (upper, lower) in enumerate(fine[-1], start=1):
        if lower is not None:
            print(f"{j}  {mp.nstr(lower, 18)}  {mp.nstr(upper, 18)}")
    print("Maximum change across both precision/quadrature runs:", mp.nstr(difference, 3))
    print("The reference values were used only for comparison.")


if __name__ == "__main__":
    main()
