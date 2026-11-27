#!/usr/bin/env python3
"""Exact arithmetic checks for the shortest positive filter and its stability.

h=1, tau=pi.  The nodes are 0,1,2,3,4.  At the frequency s=beta+i*pi
the required moments are integrals of x^k exp(s*x).  We take exp(beta)
equal to 1/2, 1, 2 with multiplicities 1, 2, 1 respectively.  All
polynomial and discrete moment calculations below use fractions.
"""

from fractions import Fraction as Q


def multiply(left, right):
    result = [Q(0)] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[i + j] += a * b
    return result


def moment(weights, radius, order):
    # x is an integer, so exp((log(radius)+i*pi)*x) = (-radius)**x.
    return sum(w * x**order * (-radius)**x for x, w in enumerate(weights))


def main():
    radii = [(Q(1, 2), 1), (Q(1), 2), (Q(2), 1)]
    weights = [Q(1)]
    for radius, multiplicity in radii:
        bernoulli = [radius / (1 + radius), 1 / (1 + radius)]
        for _ in range(multiplicity):
            weights = multiply(weights, bernoulli)
    expected = [Q(v, 36) for v in (2, 9, 14, 9, 2)]
    if weights != expected or sum(weights) != 1:
        raise AssertionError("The filter weights did not match the certificate.")
    print("Normalized grid weights: (2, 9, 14, 9, 2)/36")
    for radius, multiplicity in radii:
        for k in range(multiplicity):
            result = moment(weights, radius, k)
            if result != 0:
                raise AssertionError((radius, k, result))
            print(f"  exp(beta)={str(radius):>3}, order k={k}: moment = {result}")
        if moment(weights, radius, multiplicity) == 0:
            raise AssertionError("Unexpected extra root multiplicity.")

    # Let epsilon denote the maximum absolute moment over the four tests.
    # Split the central mass p at 2 into equal masses at 2-u and 2+u.
    # For g(x)=x^k exp(s*x) the residual is
    # p * ((g(2-u)+g(2+u))/2 - g(2)).
    # On [3/2,5/2], |s|<4 and |exp(s*x)| < 6.  For k=0,
    # |g''| < 96.  The one test k=1 has beta=0 and |g''| < 48.
    # Taylor's integral estimate therefore gives epsilon <= 48*p*u^2.
    # The beta=k=0 test gives 2*p*sin(pi*u/2)^2 >= 2*p*u^2.
    # For u<=1/2, nearest-grid distance and the splitting coupling
    # give the exact Wasserstein distance p*u.
    p = weights[2]
    print("\nCentral split by u: exact W1 and rigorous bounds for epsilon")
    print("        u          W1       lower epsilon       upper epsilon")
    for u in (Q(1, 8), Q(1, 32), Q(1, 128), Q(1, 512)):
        distance = p * u
        lower = 2 * p * u**2
        upper = 48 * p * u**2
        print(f"{str(u):>9}  {str(distance):>10}  {str(lower):>18}  {str(upper):>18}")

    # A second deformation moves the rightmost mass from 4 to 4-u.
    # The residual is p4*(g(4-u)-g(4)).  On [7/2,4], |g'|<=64
    # for k=0, and |g'|<=1+4*pi<17 for k=1, beta=0.
    # The test beta=k=0 has residual magnitude 2*p4*sin(pi*u/2)
    # >= 2*p4*u.  W1=p4*u by the coupling and difference of means.
    p4 = weights[-1]
    print("\nRight endpoint moved inward by u (0 < u <= 1/2):")
    print(f"  W1 = {p4} * u;    {2*p4} * u <= epsilon <= {64*p4} * u")
    # First-order coefficient at s=log(2)+i*pi is 16*p4*|s|;
    # at s=-log(2)+i*pi it is p4*|s|/16.  At beta=0 the two
    # coefficients are p4*pi and p4*sqrt(1+16*pi^2), both smaller.
    print(f"  limit epsilon/u = {16*p4} * sqrt(pi^2 + log(2)^2)")

    # h=1, tau=2*pi/3, harmonics 1 and 2.  At the two frequencies a
    # real polynomial vanishes iff its remainder modulo z^2+z+1 is zero.
    # Since z^3=1 at either root, this says that all three sums of
    # coefficients in a common residue class modulo three are equal.
    print("\nTwo harmonics (tau=2*pi/3), exact root-of-unity checks")
    examples = (
        ([(Q(1), 1)], [Q(1, 3)] * 3),
        ([(Q(1, 2), 1), (Q(2), 2)], [Q(v, 343) for v in (16, 48, 108, 92, 57, 18, 4)]),
    )
    for specifications, expected in examples:
        band_weights = [Q(1)]
        for radius, multiplicity in specifications:
            factor = [radius**2, radius, Q(1)]
            total = sum(factor)
            for _ in range(multiplicity):
                band_weights = multiply(band_weights, [v / total for v in factor])
        if band_weights != expected:
            raise AssertionError("The band filter coefficients differ.")
        print(f"  Width {len(band_weights)-1}; weights = " + ", ".join(map(str, band_weights)))
        for radius, multiplicity in specifications:
            for k in range(multiplicity + 1):
                sums = [Q(0)] * 3
                for x, weight in enumerate(band_weights):
                    sums[x % 3] += weight * x**k * radius**x
                vanishes = (sums[0] == sums[1] == sums[2])
                if vanishes != (k < multiplicity):
                    raise AssertionError((radius, k, sums))
                if vanishes:
                    print(f"    exp(beta)={str(radius):>3}, k={k}: both harmonic moments = 0")


if __name__ == "__main__":
    main()
