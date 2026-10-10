#!/usr/bin/env python3
"""Replay exact rank, reflection, support, and normal-form regression checks."""
from __future__ import annotations
import argparse
import csv
import json
from pathlib import Path
from fractions import Fraction as Q
from distribution import (factor, units, phi, distribution_rows, rank,
                          primitive_matrix, verify_matrix)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-q", type=int, default=60)
    ap.add_argument("--out", type=Path, default=Path(__file__).resolve().parents[1]/"data")
    args = ap.parse_args()
    if args.max_q < 3:
        ap.error("--max-q must be at least 3")
    args.out.mkdir(parents=True, exist_ok=True)
    records = []
    for q in range(2, args.max_q + 1):
        ps = list(factor(q))
        patterns = {
            "square": {p:p*p for p in ps},
            "resonant_one": {p:1 for p in ps},
            "zero": {p:0 for p in ps},
            "minus_one": {p:-1 for p in ps},
            "mixed": {p:(0 if i % 2 else p+1) for i,p in enumerate(ps)},
        }
        for label, weights in patterns.items():
            rows = distribution_rows(q, weights)
            r = rank(rows)
            assert r == q - phi(q), (q,label,r)
            anchor = [Q(int(j == 0)) for j in range(q)]
            assert rank(rows+[anchor]) == r+1
            # Even quotient: impose e_a=e_{-a}; odd quotient: e_a=-e_{-a}.
            even, odd = [], []
            for a in range(q):
                ev = [Q(0)]*q; od = [Q(0)]*q
                ev[a] += 1; ev[-a % q] -= 1
                od[a] += 1; od[-a % q] += 1
                even.append(ev); odd.append(od)
            ep, op = q-rank(rows+even), q-rank(rows+odd)
            assert (ep,op) == ((phi(q)//2,phi(q)//2) if q>2 else (1,0))
            records.append({"q":q,"pattern":label,"rank":r,
                            "dimension":q-r,"even_dimension":ep,"odd_dimension":op})
    checks = []
    for q in range(2, args.max_q+1):
        for s in (-2,-1,1,2,3):
            checks.append(verify_matrix(q,s))
    with (args.out/"exact_rank_checks.csv").open("w",newline="") as f:
        wr=csv.DictWriter(f,fieldnames=list(records[0]));wr.writeheader();wr.writerows(records)
    summary={"rank_cases":len(records),"normal_form_cases":len(checks),
             "maximum_q":args.max_q,"arithmetic":"fractions.Fraction, exact",
             "all_checks_passed":True}
    (args.out/"exact_summary.json").write_text(json.dumps(summary,indent=2)+"\n")
    certs = args.out.parent/"certificates";certs.mkdir(exist_ok=True)
    for q,s in [(12,2),(21,-1),(30,3),(60,2)]:
        C=primitive_matrix(q,s)
        payload={"q":q,"s":s,"residue_order":list(range(q)),"unit_order":units(q),
                 "C":[[str(x) for x in row] for row in C]}
        (certs/f"primitive_q{q}_s{s}.json").write_text(json.dumps(payload,indent=2)+"\n")
    print(json.dumps(summary,indent=2))


if __name__ == "__main__":
    main()
