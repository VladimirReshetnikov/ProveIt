#!/usr/bin/env python3
"""Independent depth-six audit using Pascal propagation modulo two integers.

The column recurrence used by the main certificate is not used for the
rectangle.  The centered recurrence is used only for its separate moment seed.
All comparisons are exact; primality of the moduli is unnecessary.
"""
from fractions import Fraction
from pathlib import Path
import hashlib
import json


def require(condition, description):
    if not condition:
        raise ArithmeticError(description)


def central_seed():
    # V_0(u) = product_{ell=0}^{24}(12+u-ell), through degree four.
    previous = [1, 0, 0, 0, 0]
    for ell in range(25):
        previous = [(12-ell)*previous[i] + (previous[i-1] if i else 0)
                    for i in range(5)]
    current = [2*previous[i-1] if i else 0 for i in range(5)]
    for k in range(1, 1571):
        following = [(2*current[i-1] if i else 0)
                     + k*(k+25)*previous[i] for i in range(5)]
        previous, current = current, following
    require(current[2] > 0, "central quadratic coefficient is not positive")
    require(2*current[4] > 7*current[2], "central quartic/quadratic ratio is not >7/2")
    return Fraction(current[4], current[2])


def tail_seed():
    h = sum((Fraction(1, j) for j in range(13, 3049)), Fraction())
    s = (sum((Fraction(1, j*j) for j in range(1, 3049)), Fraction())
         + sum((Fraction(1, j*j) for j in range(1, 13)), Fraction()))
    excess = h*h-s-27
    require(excess > 0, "tail rational moment part is not >27")
    return excess


def rectangle(modulus):
    maximum_k, maximum_q = 1569, 3047
    # Start just before the zero factor, then append u-q to obtain
    # H_(6,0,q) = [u^6] product_{ell=0}^{12+q}(12+u-ell).
    jet = [1, 0, 0, 0, 0, 0, 0]
    for ell in range(12):
        jet = [((12-ell)*jet[i] + (jet[i-1] if i else 0)) % modulus
               for i in range(7)]
    row = []
    for q in range(maximum_q+maximum_k+1):
        jet = [(-q*jet[i] + (jet[i-1] if i else 0)) % modulus
               for i in range(7)]
        row.append(jet[6])
    zeros, holes = set(), 0
    digest = hashlib.sha256()
    for k in range(maximum_k+1):
        for q in range(maximum_q+1):
            value = row[q]
            digest.update(f"{k},{q},{value}\n".encode("ascii"))
            if q == 12 and k % 2 == 0:
                holes += 1
                require(value == 0, f"symmetry hole failed: {modulus},{k},{q}")
            elif value == 0:
                zeros.add((k, q))
        # Independent identity from multiplication of the generating
        # series by 2+w, with the factorial scale included explicitly.
        row = [(2*row[q+1] + (k+14+q)*row[q]) % modulus
               for q in range(len(row)-1)]
    require(holes == 785, "incorrect hole count")
    return zeros, digest.hexdigest()


def main():
    ratio, tail_excess = central_seed(), tail_seed()
    unresolved, passes = None, []
    for modulus in (1000003, 1000033):
        zeros, digest = rectangle(modulus)
        unresolved = zeros if unresolved is None else unresolved & zeros
        passes.append({"modulus": modulus, "zero_nonhole_residues": len(zeros),
                       "unresolved_after_pass": len(unresolved),
                       "residue_sha256": digest})
    require(not unresolved, f"unresolved nonholes: {sorted(unresolved)}")
    result = {"status": "PASS", "method": "independent Pascal modular propagation",
              "depth": 6, "central_R": 1571, "tail_Q": 3048,
              "rectangle_k": [0, 1569], "rectangle_q": [0, 3047],
              "cells": 4785360, "symmetry_holes": 785, "nonzeros": 4784575,
              "maximum_derivative_order": 6198,
              "central_quartic_to_quadratic_ratio": str(ratio),
              "tail_rational_part_minus_27": str(tail_excess),
              "modular_passes": passes}
    destination = Path(__file__).with_name("independent_pascal_depth6.json")
    destination.write_text(json.dumps(result, indent=2)+"\n")
    print("PASS: 4785360 cells; 785 symmetry holes; 4784575 certified nonzeros")
    print("PASS: exact central and tail moment inequalities")


if __name__ == "__main__":
    main()
