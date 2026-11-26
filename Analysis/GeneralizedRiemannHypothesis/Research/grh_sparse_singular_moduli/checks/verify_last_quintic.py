#!/usr/bin/env python3
"""Build the confluent-column tables for discriminant -131 and run the residue sieve."""
from pathlib import Path
from subprocess import run
from tempfile import TemporaryDirectory
import json
import os
from math import isqrt

HERE = Path(__file__).resolve().parent
PLACES = [(601, 200), (1051, 350), (4201, 1400),
          (6301, 1050), (757, 252), (337, 112)]


def multiply(left, right, polynomial, modulus):
    """Product in (Z/modulus)[X]/polynomial, in ascending coefficient order."""
    degree = len(polynomial) - 1
    coeffs = [0] * (2 * degree - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            coeffs[i + j] += a * b
    for k in range(len(coeffs) - 1, degree - 1, -1):
        for j in range(degree):
            coeffs[k - degree + j] -= coeffs[k] * polynomial[j]
    return tuple(c % modulus for c in coeffs[:degree])


def write_table(directory, polynomial, prime, period):
    assert all(prime % t for t in range(2, 1 + isqrt(prime)))
    identity = (1, 0, 0, 0, 0)
    variable = (0, 1, 0, 0, 0)
    t = identity
    residues = []
    for _ in range(period):
        residues.append(tuple(v % prime for v in t))
        t = multiply(t, variable, polynomial, prime**2)
    # Select the scalar a as the constant coefficient modulo p^2.
    assert t[0] % prime and all(v % prime == 0 for v in t[1:])
    derivative = (0,) + tuple(v // prime for v in t[1:])
    powers = [identity]
    for _ in range(4):
        powers.append(multiply(powers[-1], derivative, polynomial, prime))
    with (directory / f"prime-{prime}.txt").open("w") as out:
        print(period, prime, file=out)
        for r in residues:
            for power in powers:
                # The distinguished exponent is 0, giving first column 1.
                # Remove its pivot row to test a four-by-four determinant.
                print(*multiply(r, power, polynomial, prime)[1:], file=out)


def main():
    data = json.loads((HERE.parent / "cm" / "class_polynomials.json").read_text())
    polynomial = data["-131"]
    assert len(polynomial) == 6 and polynomial[-1] == 1
    with TemporaryDirectory() as directory:
        work = Path(directory)
        for p, m in PLACES:
            write_table(work, polynomial, p, m)
        binary = work / "quintic_sieve"
        run([os.environ.get("CXX", "c++"), "-std=c++17", "-O3",
             str(HERE / "quintic_sieve.cpp"), "-o", str(binary)], check=True)
        run([str(binary)], cwd=work, check=True)


if __name__ == "__main__":
    main()
