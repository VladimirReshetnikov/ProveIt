#!/usr/bin/env python3
"""Generate exact rational-polynomial Herglotz remainder coefficients.

Requires SymPy.  This implements the constructive all-orders algorithm in
the article, using gamma moments and the shifted Stirling expansion.
No numerical fitting or integer-relation search is used.

Run: python truncation_coefficients.py --order 3
"""

import argparse
import sympy as sp


def coefficients(order=3):
    a, r, h, z, delta = sp.symbols("a r h z delta")
    taylor = sp.series(1 / (1 + (1 + h) ** 2), h, 0,
                      2 * order + 2).removeO()
    expectation = sp.S.Zero
    for ell in range(2 * order + 2):
        centered = sp.expand(sum(
            sp.binomial(ell, j) * (-a) ** (ell - j) * sp.rf(a + r, j)
            for j in range(ell + 1)
        ))
        expectation += taylor.coeff(h, ell) * centered / a ** ell
    expectation = sp.series(expectation.subs(a, 1 / z), z, 0,
                            order + 1).removeO()
    shifted_log_gamma = sum(
        (-1) ** (j + 1) * sp.bernoulli(j + 1, r) * z ** j / (j * (j + 1))
        for j in range(1, order + 1)
    )
    shifted_gamma = sp.series(sp.exp(shifted_log_gamma), z, 0,
                              order + 1).removeO()
    product = sp.series(2 * expectation * shifted_gamma, z, 0,
                        order + 1).removeO().expand()
    return [sp.expand(product.coeff(z, j).subs(r, 2 * delta + 2))
            for j in range(order + 1)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--order", type=int, default=3)
    args = parser.parse_args()
    if args.order < 0:
        parser.error("Order must be nonnegative")
    for j, polynomial in enumerate(coefficients(args.order)):
        print(f"C_{j}(delta) = {polynomial}")


if __name__ == "__main__":
    main()
