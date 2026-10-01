#!/usr/bin/env python3
"""Independent depth-five audit using Pascal propagation modulo three integers.

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
    # V_0(u) = product_{ell=0}^{20}(10+u-ell), through degree three.
    previous = [1, 0, 0, 0]
    for ell in range(21):
        previous = [(10-ell)*previous[i] + (previous[i-1] if i else 0)
                    for i in range(4)]
    current = [2*previous[i-1] if i else 0 for i in range(4)]
    for k in range(1, 410):
        following = [(2*current[i-1] if i else 0)
                     + k*(k+21)*previous[i] for i in range(4)]
        previous, current = current, following
    require(current[1] > 0, "central linear coefficient is not positive")
    require(current[3] > 8*current[1], "central cubic/linear ratio is not >8")
    return Fraction(current[3], current[1])


def tail_seed():
    h = sum((Fraction(1, j) for j in range(11, 840)), Fraction())
    s = (sum((Fraction(1, j*j) for j in range(1, 840)), Fraction())
         + sum((Fraction(1, j*j) for j in range(1, 11)), Fraction()))
    excess = h*h-s-16
    require(excess > 0, "tail rational moment part is not >16")
    return excess


def rectangle(modulus):
    maximum_k, maximum_q = 408, 838
    # Start just before the zero factor, then append u-q to obtain
    # H_(5,0,q) = [u^5] product_{ell=0}^{10+q}(10+u-ell).
    jet = [1, 0, 0, 0, 0, 0]
    for ell in range(10):
        jet = [((10-ell)*jet[i] + (jet[i-1] if i else 0)) % modulus
               for i in range(6)]
    row = []
    for q in range(maximum_q+maximum_k+1):
        jet = [(-q*jet[i] + (jet[i-1] if i else 0)) % modulus
               for i in range(6)]
        row.append(jet[5])
    zeros, holes = set(), 0
    digest = hashlib.sha256()
    for k in range(maximum_k+1):
        for q in range(maximum_q+1):
            value = row[q]
            digest.update(f"{k},{q},{value}\n".encode("ascii"))
            if q == 10 and k % 2 == 1:
                holes += 1
                require(value == 0, f"symmetry hole failed: {modulus},{k},{q}")
            elif value == 0:
                zeros.add((k, q))
        # Independent identity from multiplication of the generating
        # series by 2+w, with the factorial scale included explicitly.
        row = [(2*row[q+1] + (k+12+q)*row[q]) % modulus
               for q in range(len(row)-1)]
    require(holes == 204, "incorrect hole count")
    return zeros, digest.hexdigest()


def main():
    ratio, tail_excess = central_seed(), tail_seed()
    unresolved, passes = None, []
    for modulus in (1009, 1013, 1019):
        zeros, digest = rectangle(modulus)
        unresolved = zeros if unresolved is None else unresolved & zeros
        passes.append({"modulus": modulus, "zero_nonhole_residues": len(zeros),
                       "unresolved_after_pass": len(unresolved),
                       "residue_sha256": digest})
    require(not unresolved, f"unresolved nonholes: {sorted(unresolved)}")
    result = {"status": "PASS", "method": "independent Pascal modular propagation",
              "depth": 5, "central_R": 410, "tail_Q": 839,
              "rectangle_k": [0, 408], "rectangle_q": [0, 838],
              "cells": 343151, "symmetry_holes": 204, "nonzeros": 342947,
              "maximum_derivative_order": 1665,
              "central_cubic_to_linear_ratio": str(ratio),
              "tail_rational_part_minus_16": str(tail_excess),
              "modular_passes": passes}
    destination = Path(__file__).with_name("independent_pascal_depth5.json")
    destination.write_text(json.dumps(result, indent=2)+"\n")
    print("PASS: 343151 cells; 204 symmetry holes; 342947 certified nonzeros")
    print("PASS: exact central and tail moment inequalities")


if __name__ == "__main__":
    main()
