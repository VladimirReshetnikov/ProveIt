"""Numerical checks of the all-orders angular-zero theorem (not intervals)."""
from __future__ import annotations
from fractions import Fraction
from pathlib import Path
import argparse
import json
import mpmath as mp
import sympy as sp
from derive_angular import derive


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--output', default='angular_numeric.json')
    args=ap.parse_args()
    expansion,_=derive(Fraction(2,13))
    rows=[]
    for a in [16,32,64,128,256]:
        mp.mp.dps=max(80,int(a*0.9)+60)
        for b in [1,2,4]:
            harmonic=mp.mpf(0)
            coefficients=[]
            H={}
            for n in range(2,513):
                harmonic+=mp.mpf(1)/(n-1)**b
                H[n-1]=harmonic
                coefficients.append((n,harmonic*(mp.mpf(2)/n)**a))
            def f(delta):
                total=mp.mpf(0)
                for n,c in coefficients:
                    quadrant=n%4
                    trig=(mp.sin(n*delta) if quadrant==2 else
                          -mp.sin(n*delta) if quadrant==0 else
                          mp.cos(n*delta) if quadrant==1 else -mp.cos(n*delta))
                    total+=c*trig
                return total
            guess=H[2]*(mp.mpf(2)/3)**a/2
            root=mp.findroot(f,(guess*mp.mpf('.9'),guess*mp.mpf('1.1')))
            approx=mp.mpf(0)
            for base,c in expansion.items():
                value=mp.mpf(0)
                for monomial,coeff in sp.Poly(c,*sorted(c.free_symbols,key=str)).terms():
                    term=mp.mpf(int(sp.numer(coeff)))/int(sp.denom(coeff))
                    for symbol,power in zip(sorted(c.free_symbols,key=str),monomial):
                        term*=H[int(str(symbol)[1:])]**power
                    value+=term
                approx+=value*(mp.mpf(base.numerator)/base.denominator)**a
            error=root-approx
            tail=mp.mpf(2)**a*mp.mpf(512)**(1-a)*((1+mp.log(512))/(a-1)+mp.mpf(1)/(a-1)**2)
            if tail > abs(error)*mp.mpf('1e-20'):
                raise ArithmeticError('Fourier tail not small enough for the diagnostic')
            rows.append({'a':a,'b':b,'working_digits':mp.mp.dps,'delta':mp.nstr(root,38),'ten_term_absolute_error':mp.nstr(abs(error),12),'normalized_error':mp.nstr(error/(mp.mpf(2)/13)**a,18),'predicted_limit':mp.nstr(-H[12]/2,18),'normalized_fourier_tail_bound':mp.nstr(tail,8),'check_type':'high-precision diagnostic; rounding not interval-certified'})
    Path(args.output).parent.mkdir(parents=True, exist_ok=True)
    Path(args.output).write_text(json.dumps({'rows':rows},indent=2)+'\n')
    print(json.dumps({'cases':len(rows),'first':rows[0],'last':rows[-1]},indent=2))


if __name__=='__main__':
    main()
