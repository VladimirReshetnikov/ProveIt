#!/usr/bin/env python3
"""Certify local hypotheses, compile the C++ checker, and run each width test."""
import argparse
from fractions import Fraction
import json
import os
from pathlib import Path
import subprocess
import tempfile
from cm_all_orders import translated_polynomial, strict_ball_count, threshold, valuation

CASES={87:(23,19,Fraction(3)), 131:(17,8,Fraction(3)), 348:(29,2,Fraction(3,2)),
       432:(23,19,Fraction(3)), 675:(17,8,Fraction(3))}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--width',type=int,default=32768)
    parser.add_argument('--case',type=int,choices=CASES)
    args=parser.parse_args()
    polynomials=json.loads(Path(__file__).with_name('cm-extended-polys.json').read_text())
    polynomials['131']=json.loads(Path(__file__).with_name('cm-all-polys.json').read_text())['131']
    with tempfile.TemporaryDirectory() as tmp:
        exe=Path(tmp)/'width'
        subprocess.run([os.environ.get('CXX','c++'),'-O3','-std=c++17',str(Path(__file__).with_suffix('.cpp')),'-o',exe],check=True)
        for D,(p,r,v) in CASES.items():
            if args.case and D!=args.case:
                continue
            P=polynomials[str(D)]
            degree=len(P)-1
            assert degree in (5,6) and P[-1]==1 and P[0]
            # An equality slope v of the lower Newton polygon means an
            # actual root has exactly this valuation by the polygon theorem.
            weighted=[(valuation(c,p)+i*v,i) for i,c in enumerate(P) if c]
            low=min(z for z,i in weighted)
            assert sum(z==low for z,i in weighted)>=2
            theta=threshold(4,p)
            shifted=translated_polynomial(P,p,0,r)
            assert strict_ball_count(shifted,p,theta)>=4
            inputs=' '.join(map(str,[degree,p,v.numerator,v.denominator,*P[:-1]]))+'\n'
            print(f'D={D} p={p} center={r} unit_depth>{theta} outlier_v={v}', flush=True)
            subprocess.run([exe,str(args.width)],input=inputs,text=True,check=True)
if __name__=='__main__':
    main()
