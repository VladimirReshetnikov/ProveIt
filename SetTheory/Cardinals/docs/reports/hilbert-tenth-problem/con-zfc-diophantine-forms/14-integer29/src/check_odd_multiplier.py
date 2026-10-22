#!/usr/bin/env python3
"""Small diagnostics for the new odd auxiliary multiplier.

These cases check algebraic identities. They do not prove the K215 reduction,
materialize its enormous coefficients, or assert a K215 halting tuple.
"""

import argparse
import json
from pathlib import Path


def pell(parameter, index):
    x, y = 1, 0
    for _ in range(index):
        x, y = parameter*x + (parameter*parameter-1)*y, x + parameter*y
    return x, y


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path,
                    default=Path(__file__).resolve().parents[1] / 'data' / 'odd_multiplier_toy_checks.json')
    args = ap.parse_args()
    rows = []
    for a in range(2, 9):
        rank = 3
        _, c = pell(a, rank)
        f, auxiliary_y = pell(a, c*rank)
        assert auxiliary_y % (c*c) == 0
        normalized_i = auxiliary_y // (c*c)
        assert normalized_i % 2 == 1
        delta = a*a-1
        rho = delta*auxiliary_y
        v, y = 4*rho*rho-3, 4*rho*rho-1
        assert rho*rho*v*v - (rho*rho-1)*y*y == 1
        assert (v+c) % f == 0
        assert (v+rank) % c == 0
        o = (v+c)//f
        assert (o+rank*f) % c == 0
        t = (o+rank*f)//c
        assert c*(t*f-1)-rank*f*f == v
        if a % 2 == 0:
            assert delta*normalized_i % 2 == 1
        rows.append({
            "A": a, "R": rank, "c": c, "m": c*rank,
            "i_odd": True, "quotient_reconstruction": True,
            "f_bits": f.bit_length(),
        })
    result = {
        "scope": "Finite algebra diagnostics only, not proof of the full K215 reduction",
        "cases": rows,
    }
    output = args.output
    output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
