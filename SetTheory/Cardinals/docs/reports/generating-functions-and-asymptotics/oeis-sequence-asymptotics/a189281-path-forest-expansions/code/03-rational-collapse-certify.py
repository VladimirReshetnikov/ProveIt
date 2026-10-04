#!/usr/bin/env python3
"""Exact Bonferroni certificates using the proved single-sum moment formula.

Python standard library only. Run from any working directory.
The reported decimal intervals are outward-rounded from exact fractions.
"""
from fractions import Fraction
from math import factorial
from pathlib import Path
import json
from verify import stable_mu, correction_polynomials


def interval_text(lo: Fraction, hi: Fraction, places: int = 8) -> str:
    scale = 10**places
    a = (lo*scale).__floor__()
    b = (hi*scale).__ceil__()
    def fixed(z: int) -> str:
        sign = '-' if z < 0 else ''
        z = abs(z)
        return f'{sign}{z//scale}.{z%scale:0{places}d}'
    return f'[{fixed(a)}, {fixed(b)}]'


def main() -> None:
    out = Path(__file__).resolve().parents[1]/'data'
    out.mkdir(parents=True, exist_ok=True)
    B = correction_polynomials(12,2,2)
    c = [sum((-1)**h*v for h,v in enumerate(row)) for row in B]
    emin = sum(Fraction((-1)**k,factorial(k)) for k in range(102))
    emax = emin + Fraction(1,factorial(102))
    assert 0 < emin < emax
    records=[]
    lines=[]
    for n in (64,128,256):
        mu=[stable_mu(n,k,2,2) for k in range(32)]
        upper=sum((-1)**k*mu[k] for k in range(31))
        lower=upper-mu[31]
        assert 0 < lower <= upper < 1
        for M in (4,8):
            trunc=sum(Fraction(c[j],n**j) for j in range(M+1))
            lo=n**(M+1)*(lower/emax-trunc)
            hi=n**(M+1)*(upper/emin-trunc)
            assert lo<=hi
            text=interval_text(lo,hi)
            lines.append(f'n={n}, M={M}, scaled residual: {text}; limit={c[M+1]}')
            records.append({'n':n,'M':M,'lower':str(lo),'upper':str(hi),
                            'outward_decimal':text,'asymptotic_limit':c[M+1]})
    (out/'bonferroni.json').write_text(json.dumps(records,indent=2)+'\n')
    (out/'bonferroni.txt').write_text('\n'.join(lines)+'\n')
    print('\n'.join(lines))

if __name__=='__main__':
    main()
