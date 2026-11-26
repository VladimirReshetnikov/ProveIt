#!/usr/bin/env python3
"""Check the six-field splitting rule at good primes through 5000."""
import csv
import json
from collections import Counter
from math import prod
from pathlib import Path

from reflection import prime


def main():
    from sympy import Poly, Symbol
    x = Symbol("x")
    with (Path(__file__).resolve().parents[1] / "data/reflected_fields.csv").open() as f:
        rows = list(csv.DictReader(f))
    results = {}
    for d in (-12451,-37363):
        family = [(int(r["p"]),int(r["a"]),int(r["b"])) for r in rows if int(r["D"]) == d]
        assert len(family) == 6
        bad = 10*d*prod(b for _,_,b in family)
        counts, witnesses = Counter(), {}
        for r in range(7,5001):
            if not prime(r) or bad % r == 0:
                continue
            sign = 1 if pow(d,(r-1)//2,r) == 1 else -1
            multiplier = r*sign % 5
            # A test of literal polynomial root counts, independent of Kummer residues.
            roots = [sum((t*(t*t*(t*t-5*p)+5*p*p)-a) % r == 0 for t in range(r))
                     for p,a,b in family]
            if multiplier == 1:
                assert sorted(roots) in ([0]*5+[5],[5]*6), (d,r,roots)
                kind = "all split" if min(roots) == 5 else "only line " + str(roots.index(5)+1)
            else:
                assert roots == [1]*6, (d,r,roots)
                kind = "1+2+2" if multiplier == 4 else "1+4"
            counts[kind] += 1
            if kind not in witnesses:
                patterns = []
                for p,a,b in family:
                    poly = Poly(x**5-5*p*x**3+5*p*p*x-a, x, modulus=r)
                    _, factors = poly.factor_list()
                    assert all(e == 1 for g,e in factors)
                    patterns.append(sorted(g.degree() for g,e in factors))
                if multiplier == 1:
                    assert all(v == ([1]*5 if n == 5 else [5]) for v,n in zip(patterns,roots))
                else:
                    assert all(v == ([1,2,2] if multiplier == 4 else [1,4]) for v in patterns)
                witnesses[kind] = r
        assert len(witnesses) == 9
        results[d] = dict(checked=sum(counts.values()), counts=dict(sorted(counts.items())),
                          first_prime=dict(sorted(witnesses.items())))
    print(json.dumps(results,indent=2))


if __name__ == "__main__":
    main()
