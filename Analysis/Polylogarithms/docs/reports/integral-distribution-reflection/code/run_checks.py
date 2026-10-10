#!/usr/bin/env python3
"""Reproduce exact unit-minor, polynomial, scalar-parity and jet checks."""
from __future__ import annotations
import argparse
from itertools import product
from pathlib import Path
import json
from distribution import (layout, normal_forms, check_all_rows, certificate,
                          parity_case, jet_case)
from verify_certificates import verify
ROOT = Path(__file__).resolve().parents[1]

if not __debug__:
    raise RuntimeError('Run without -O: exact validation uses assertions.')


def write(name, obj):
    path = ROOT/'data'/name
    path.write_text(json.dumps(obj, indent=2, sort_keys=True)+'\n', encoding='utf-8')

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--polynomial-max', type=int, default=120)
    ap.add_argument('--parity-max', type=int, default=500)
    args = ap.parse_args()
    poly = []
    for q in range(2, args.polynomial_max+1):
        g, nf = normal_forms(q)
        rows = check_all_rows(q, nf)
        for a, vector in nf.items():
            for (b, ex), c in vector.items():
                assert all(e <= h for e, h in zip(ex, g['heights'][a]))
            W = (len(g['primes'])+1)*sum(g['heights'][a])+len(g['bad'][a])
            assert sum(abs(c) for c in vector.values()) <= max(g['primes'])**W
        poly.append(dict(q=q, basis_size=len(g['basis']), raw_rows=rows,
                         max_coefficient=max(abs(c) for v in nf.values() for c in v.values()),
                         total_terms=sum(len(v) for v in nf.values()),
                         degree_and_height_bounds=True))
    write('polynomial_checks.json', {'range':[2,args.polynomial_max], 'cases':poly})
    receipts=[]
    for q in [12,15,30,60,72,105,120]:
        path=ROOT/'data'/f'normal_forms_q{q}.json'
        path.write_text(json.dumps(certificate(q), indent=2)+'\n', encoding='utf-8')
        receipts.append(verify(path))
    write('certificate_checks.json', receipts)
    binary=[]
    levels=list(range(2,args.parity_max+1))+[840,1260,2310]
    for q in levels:
        for bits in product([0,1],repeat=len(layout(q)['primes'])):
            binary.append(parity_case(q,bits))
    write('parity_checks.json',{'levels_through':args.parity_max,
          'additional_levels':[840,1260,2310], 'case_count':len(binary),
          'raw_row_checks':sum(c['raw_rows_checked'] for c in binary), 'cases':binary})
    jets=[]
    for q in [3,4,6,9,12,15,20,24,30,60]:
        r=len(layout(q)['primes'])
        for L in [1,2,3]:
            for weights in product(range(1<<L),repeat=r):
                jets.append(jet_case(q,L,weights))
    for q,L,weights in [(15,5,(1+4,1+8)),(12,4,(1+2,1+8)),
                       (9,5,(1+8,)),(60,5,(4,1+8,1+16)),
                       (2,7,(43,))]:
        jets.append(jet_case(q,L,weights))
    write('jet_checks.json', {'case_count':len(jets),'cases':jets})
    summary=dict(polynomial_levels=len(poly), polynomial_raw_rows=sum(c['raw_rows'] for c in poly),
                 polynomial_symbols=sum(c['q'] for c in poly),
                 independent_certificates=len(receipts),
                 independent_certificate_identities=sum(c['identities_verified'] for c in receipts),
                 independent_certificate_raw_rows=sum(c['raw_rows_verified'] for c in receipts),
                 scalar_parity_cases=len(binary), scalar_binary_raw_rows=sum(c['raw_rows_checked'] for c in binary),
                 jet_cases=len(jets), status='all exact checks passed')
    write('checks_summary.json',summary)
    print(json.dumps(summary,indent=2))
if __name__=='__main__': main()
