#!/usr/bin/env python3
"""Certify the final four degree-six cases for five-term equations."""
import json
import os
from math import isqrt
from pathlib import Path
from subprocess import run
from tempfile import TemporaryDirectory
from verify_last_quintic import multiply

HERE = Path(__file__).resolve().parent
WITNESSES = {
    87: [(103, 102), (1531, 1530), (151, 150), (487, 486), (1459, 486)],
    348: [(487, 486), (1459, 486)],
    432: [(109, 36), (433, 144)],
    675: [(241, 40), (13, 56)],
}


def write_table(folder, D, H, p, m):
    assert all(p % k for k in range(2, isqrt(p) + 1))
    assert len(H) == 7 and H[-1] == 1
    one, variable = (1, 0, 0, 0, 0, 0), (0, 1, 0, 0, 0, 0)
    t = one
    residues = []
    for _ in range(m):
        residues.append(tuple(z % p for z in t))
        t = multiply(t, variable, H, p*p)
    assert t[0] % p != 0 and all(z % p == 0 for z in t[1:])
    deriv = (0,) + tuple(z // p for z in t[1:])
    powers = [one]
    for _ in range(4):
        powers.append(multiply(powers[-1], deriv, H, p))
    with (folder / f"{D}-{p}.txt").open("w") as f:
        print(m, p, file=f)
        for r in residues:
            for power in powers:
                # Delete the constant coordinate: exponent zero supplies its pivot.
                print(*multiply(r, power, H, p)[1:], file=f)


def main():
    data = json.loads((HERE / "five_small_witnesses.json").read_text())
    with TemporaryDirectory() as tmp:
        folder = Path(tmp)
        for D, tests in WITNESSES.items():
            for p, m in tests:
                write_table(folder, D, data[str(D)]["coefficients"], p, m)
        binary = folder / "five_sieves"
        run([os.environ.get("CXX", "c++"), "-O3", "-std=c++17",
             str(HERE / "five_sieves.cpp"), "-o", str(binary)], check=True)
        run([str(binary)], check=True, cwd=folder)


if __name__ == "__main__":
    main()
