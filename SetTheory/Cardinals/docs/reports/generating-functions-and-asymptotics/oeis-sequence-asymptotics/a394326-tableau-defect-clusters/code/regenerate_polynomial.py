#!/usr/bin/env python3
"""Regenerate N_H8.json using standard-library exact Newton interpolation.

The matrix is independently constructed in the ungauged q coordinate. The
Leibniz row-degree bound is 239, so its exact values at 0,...,239 determine
its polynomial. Newton forward differences give an exact reconstruction.
No SymPy, floating-point interpolation, or preexisting polynomial is used.
The adjugate remains supplied proof data, independently verified coefficient
by coefficient against the reconstructed genuine determinant.
"""
import argparse
import json
import math
from fractions import Fraction as F
from pathlib import Path
from certify_rational_circle import (H, states, polynomial_matrix,
                                    bareiss_integer_determinant, require)


def run():
    matrix = polynomial_matrix(states(H), False)
    bound = sum(max((e for cell in row for e in cell), default=0) for row in matrix)
    differences = []
    for q in range(bound+1):
        value = [[sum(c*q**e for e, c in cell.items()) for cell in row] for row in matrix]
        differences.append(bareiss_integer_determinant(value))
    coefficients = [F(0)]*(bound+1)
    falling = [1]
    for k in range(bound+1):
        factor = F(differences[0], math.factorial(k))
        for j, c in enumerate(falling):
            coefficients[j] += factor*c
        differences = [b-a for a, b in zip(differences, differences[1:])]
        nxt = [0]*(len(falling)+1)
        for j, c in enumerate(falling):
            nxt[j] -= k*c
            nxt[j+1] += c
        falling = nxt
    require(all(c.denominator == 1 for c in coefficients), 'nonintegral determinant coefficient')
    result = [int(c) for c in coefficients]
    while result and result[-1] == 0:
        result.pop()
    require(len(result) == 162 and result[0] == 1, 'unexpected regenerated polynomial')
    return {'H': H, 'coeffs': result}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    text = json.dumps(run(), indent=2)+'\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
