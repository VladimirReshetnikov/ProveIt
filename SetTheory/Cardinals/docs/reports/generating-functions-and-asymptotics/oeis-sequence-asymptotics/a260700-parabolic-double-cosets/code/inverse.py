#!/usr/bin/env python3
"""Numerical inverse diagnostics; these do not certify finite asymptotic constants."""
import argparse
import json
from pathlib import Path
import mpmath as mp
import sympy as sp

ROOT=Path(__file__).resolve().parent.parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output-dir',type=Path,default=Path('replay-output'))
args=parser.parse_args();OUT=args.output_dir.resolve();OUT.mkdir(parents=True,exist_ok=True)
mp.mp.dps=150
r=mp.log(2);K=mp.exp(-r*r/2)/(4*r*r)
symr=sp.Symbol('r')
co=json.loads((ROOT/'data/coefficients-order4.json').read_text())
B=[mp.mpf(str(sp.N(sp.sympify(x).subs(symr,sp.log(2)),160))) for x in co['B']]
p=list(map(int,json.loads((ROOT/'data/exact-values.json').read_text())['p']))

def logF(x,m):
    return mp.log(K)+mp.loggamma(x+1)-2*x*mp.log(r)+mp.log(sum(B[j]/x**j for j in range(m+1)))

def derivative(x,m):
    P=sum(B[j]/x**j for j in range(m+1))
    dP=sum(-j*B[j]/x**(j+1) for j in range(1,m+1))
    return mp.digamma(x+1)-2*mp.log(r)+dP/P

def inverse(y,m):
    Y=mp.log(y);x0=Y/mp.lambertw(Y/(mp.e*r*r))
    return mp.findroot(lambda x:logF(x,m)-Y,(x0-1,x0+1))

rows=[]
for n in (25,100,400):
    y=mp.mpf(p[n]);Y=mp.log(y);w=mp.lambertw(Y/(mp.e*r*r));x0=Y/w;D=1+w
    A=mp.log(2*mp.pi*x0)/2+mp.log(K);C1=mp.mpf(1)/12+B[1]
    approx=x0-A/D-(A*A/(2*D*D)-A/(2*D)+C1)/(x0*D)
    root=inverse(y,4);x=x0;errs=[x-root]
    for _ in range(3):
        x-= (logF(x,4)-Y)/derivative(x,4);errs.append(x-root)
    assert all(abs(errs[i+1])<abs(errs[i]) for i in range(3))
    assert abs(logF(root,4)-Y)<mp.mpf('1e-130')
    rows.append({'n':n,'F4_inverse_minus_integer':mp.nstr(root-n,45),
                 'explicit_inverse_formula_error':mp.nstr(approx-root,45),
                 'newton_errors_steps0to3':[mp.nstr(v,45) for v in errs]})
y=p[25]+1;x=inverse(mp.mpf(y),1)
actual=next(i for i,value in enumerate(p) if value>=y)
assert actual==26 and int(mp.ceil(x))==25
out={'scope':'Numerical diagnostics only; no effective O-constant or finite-n certificate is inferred',
     'precision_decimal_digits':mp.mp.dps,'rows':rows,
     'rounding_counterexample':{'input':'p_25+1','actual_threshold':actual,'ceil_inverse_F1':int(mp.ceil(x)),
                               'inverse_F1':mp.nstr(x,80)}}
(OUT/'inverse-validation.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
