#!/usr/bin/env python3
"""Independent maximal-order discriminant checks using SymPy."""
import csv
from pathlib import Path

from sympy import Poly, Symbol, __version__
from sympy.polys.numberfields import round_two

DATA = Path(__file__).resolve().parents[1] / "data"


def main():
    x = Symbol("x")
    n = 0
    with (DATA / "reflected_fields.csv").open() as stream:
        for row in csv.DictReader(stream):
            d, p, a, b = (int(row[k]) for k in ("D", "p", "a", "b"))
            assert a*a - d*b*b == 4*p**5
            polynomial = Poly(x**5 - 5*p*x**3 + 5*p*p*x - a, x)
            assert polynomial.is_irreducible
            _, discriminant = round_two(polynomial)
            assert discriminant == int(row["field_discriminant"]), (d,p)
            index = int(row["power_basis_index"])
            assert discriminant * index**2 == polynomial.discriminant()
            n += 1
    cyclotomic = Poly(x**5 + x**4 - 4*x**3 - 3*x**2 + 3*x + 1,x)
    assert cyclotomic.is_irreducible and round_two(cyclotomic)[1] == 11**4
    print(f"SymPy {__version__}: {n} reflected quintics and the cyclotomic quintic passed.")


if __name__ == "__main__":
    main()
