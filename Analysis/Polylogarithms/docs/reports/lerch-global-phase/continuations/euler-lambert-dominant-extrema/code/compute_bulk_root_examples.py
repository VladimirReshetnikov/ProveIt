#!/usr/bin/env python3
"""Exact rational isolation of small-degree Lambert roots for a CDF figure.

Uses SymPy's polynomial isolation over QQ, not floating point root finding.
The finite examples illustrate, and do not prove, the limiting zero law.
"""
import argparse
import json
from pathlib import Path
from fractions import Fraction
import sympy as sp
from verify_diagonal_inverse import stirling_polynomials

ROOT=Path(__file__).resolve().parents[1]

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--degrees',type=int,nargs='+',default=[12,30,60])
    parser.add_argument('--output',type=Path,default=ROOT/'data/bulk_root_examples.json')
    args=parser.parse_args()
    polys=stirling_polynomials(max(args.degrees))
    x=sp.Symbol('x')
    rows=[]
    for n in args.degrees:
        coefficients=[sp.Rational(c.numerator,c.denominator) for c in reversed(polys[n])]
        polynomial=sp.Poly.from_list(coefficients,gens=x)
        intervals=polynomial.intervals(eps=sp.Rational(1,10**14))
        assert len(intervals)==n and all(multiplicity==1 for _,multiplicity in intervals)
        roots=[]
        for (lo,hi),multiplicity in intervals:
            if lo==hi==0:
                continue
            assert lo>0
            roots.append({'lower':str(lo),'upper':str(hi),
                          'midpoint':str(sp.N((lo+hi)/2,25))})
        assert len(roots)==n-1
        rows.append({'n':n,'positive_roots':roots})
        print(f'Isolated all {n-1} positive roots for degree {n}.',flush=True)
    report={'status':'exact rational polynomial root isolation for finite examples',
            'sympy_version':sp.__version__,'maximum_interval_width':'1/100000000000000',
            'warning':'These finite examples are not premises of the asymptotic theorem.',
            'rows':rows}
    args.output.write_text(json.dumps(report,indent=2)+'\n')

if __name__=='__main__':
    main()
