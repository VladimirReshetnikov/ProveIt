#!/usr/bin/env python3
"""Exhaustive checks of partial arrangement counts and extension bookkeeping."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json

from arrangements import count, count_partial


def literal_partial(table, q):
    n, m = len(table), len(table[0])
    good = valid = total = 0
    for h, a, b, c in product(range(m), range(n), range(n), range(n)):
        xs = (a,b,c,(a+b-c) % n)
        for ys in product(range(m), repeat=4):
            total += 1
            values = [(table[x][y],table[x][(y+h) % m]) for x,y in zip(xs,ys)]
            if any(u is None or v is None for u,v in values):
                continue
            valid += 1
            ds = [v-u for u,v in values]
            good += (ds[0]+ds[1]-ds[2]-ds[3]) % q == 0
    return good, valid, total


def run():
    tested = no_valid = 0
    for vals in product((None,0,1), repeat=6):
        table = [list(vals[2*x:2*x+2]) for x in range(3)]
        tau = F(sum(v is None for v in vals),6)
        assert count_partial(table,2,4) == literal_partial(table,2)
        good4, _, total4 = count_partial(table,2,4)
        theta4 = F(good4,total4)
        for s in (4,6,16):
            good, valid, total = count_partial(table,2,s)
            assert F(valid,total) >= 1-2*s*tau
            theta_s = F(good,total)
            assert theta_s >= F(s,4)*theta4-(F(s,4)-1)
            assert theta_s >= theta4**(s//2-1)
            for fill in (0,1):
                extended = [[fill if v is None else v for v in row] for row in table]
                full_good, full_total = count(extended,2,s)
                assert full_total == total and full_good >= good
                if valid:
                    eta, lam = F(valid-good,valid), F(valid,total)
                    effective = lam*eta+1-lam
                    assert F(total-full_good,total) <= effective
                    assert effective <= eta+2*s*tau
            if s == 4:
                no_valid += valid == 0
        tested += 1
    output = {"status":"PASS", "partial_tables":tested, "n":3,"m":2,"q":2,
              "orders":[4,6,16], "s4_literal_enumeration":True,
              "constant_extensions_per_table":2,
              "tables_with_no_valid_arrangement":no_valid,
              "arithmetic":"exact Python integers and fractions.Fraction"}
    path=Path(__file__).resolve().parents[1]/'data'/'erasure_verification.json'
    path.write_text(json.dumps(output,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(output,indent=2))


if __name__ == '__main__':
    run()
