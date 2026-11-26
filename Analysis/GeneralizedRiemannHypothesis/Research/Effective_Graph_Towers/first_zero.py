#!/usr/bin/env python3
"""Find the first p-power torsion zero of an integral Laurent polynomial.

Usage:
  python first_zero.py 3 '[[1,[0]],[1,[3]],[1,[6]]]'
  python first_zero.py 3 terms.json

Output gives occurrence, least level h, and integer exponents for the coordinates
relative to a common primitive root of order p^h. For Phi_9 the answer is h=2
with exponents [1]. A finite state search decides whether any zero exists. At
the first accepted level an independent cyclotomic reduction recovers a witness.
"""
import argparse
import json
from collections import defaultdict
from itertools import product
from pathlib import Path

from tower_automaton import Compiler


def vanishes(p, h, vector, terms):
    """Fold monomials modulo Z^(p^h)-1 and reduce modulo Phi_(p^h)(Z)."""
    modulus = p**h
    block = modulus // p
    groups = defaultdict(lambda: [0] * p)
    for coefficient, exponents in terms:
        j = sum(a * b for a, b in zip(exponents, vector)) % modulus
        top, low = divmod(j, block)
        groups[low][top] += coefficient
    return all(all(c == top_row[-1] for c in top_row) for top_row in groups.values())


def witness(p, h, d, terms):
    modulus = p**h
    for pivot in range(d):
        # Normalize the first unit coordinate to exactly one.
        ranges = ([range(0, modulus, p)] * pivot + [(1,)]
                  + [range(modulus)] * (d - pivot - 1))
        for vector in product(*ranges):
            if vanishes(p, h, vector, terms):
                return list(vector)
    raise ArithmeticError("accepted conductor had no zero in direct cyclotomic reduction")


def first_zero(p, terms):
    try:
        c = Compiler(p, terms, omit_zeros=True)
    except ValueError as error:
        if str(error) != "zero polynomial":
            raise
        return {"occurs": True, "first_level": 0, "coordinate_exponents": [0] * len(terms[0][1])}
    if sum(c.coeffs) == 0:
        return {"occurs": True, "first_level": 0, "coordinate_exponents": [0] * c.d}
    frontier = set(c.starts())
    seen = set(frontier)
    h = 0
    while frontier:
        h += 1
        following = set()
        for state in frontier:
            _, blocks, accepted = c.transitions(state)
            if accepted:
                return {"occurs": True, "first_level": h,
                        "coordinate_exponents": witness(p, h, c.d, terms)}
            following.update(blocks)
        frontier = following - seen
        seen.update(frontier)
    return {"occurs": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("p", type=int)
    parser.add_argument("terms", help="JSON array of [coefficient, exponent tuple] entries, or its path")
    args = parser.parse_args()
    raw = args.terms.strip()
    terms = json.loads(raw if raw.startswith("[") else Path(raw).read_text())
    print(json.dumps(first_zero(args.p, terms), indent=2))


if __name__ == "__main__":
    main()
