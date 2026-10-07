#!/usr/bin/env python3
"""Exact frozen-coefficient identities; optional decimal diagnostics are not intervals."""
import argparse
import json
from pathlib import Path
import sympy as S
from generate_coefficients import r
ROOT=Path(__file__).resolve().parents[1]

def zero(expr,label):
    if S.cancel(expr) != 0: raise ArithmeticError(label)

def verify():
    data=json.loads((ROOT/'data/coefficients_order3.json').read_text())
    C={k:[S.sympify(z,locals={'r':r}) for z in seq] for k,seq in data['coefficients'].items()}
    v1=r*r*(r-6)*(r+3)/48
    v2=r**3*(r**8-3*r**7-66*r**6+58*r**5+945*r**4+813*r**3-2640*r*r-4956*r-2208)/(4608*(r+1)**3)
    zero(C['V_over_Bell'][1]-v1,'v1')
    zero(C['V_over_Bell'][2]-v2,'v2')
    zero(S.limit(C['V_over_Bell'][3]/r**12,r,S.oo)-S.Rational(1,663552),'v3 leading term')
    for j in [1,2]: zero(C['L'][j]-C['U'][j],f'U/L order {j}')
    zero(C['L'][3]-C['U'][3]+r**6/48,'U/L order 3')
    old=json.loads((ROOT/'data/coefficients_order2.json').read_text())['coefficients']
    for name,seq in old.items():
        for j,value in enumerate(seq):
            zero(S.sympify(value,locals={'r':r})-C[name][j],f'cross-order {name} {j}')
    # Independent first coefficient using the first two Gaussian phase terms.
    y=S.symbols('y')
    E1=(2*r+1)*y**3/6+(r*r+r-1)*y/2
    E2=-(3*r+1)*y**4/12+(S.Rational(1,4)-r/2-3*r*r/4)*y*y-S.Rational(1,12)+r/4-r*r/4-r**3/12
    def gaussian(f):
        return S.factor(sum(c*S.factorial2(k-1)/(r+1)**(k//2) for (k,),c in S.Poly(S.expand(f),y).terms() if k%2==0))
    for name,p1 in [('H',0),('V',-S.Rational(1,2)),('U',S.Rational(1,2)),('L',S.Rational(1,2))]:
        zero(C[name][1]-r/2*gaussian(E2+E1**2/2+p1*r),f'independent first coefficient {name}')
    return {'status':'passed','exact_identity_checks':28,'symbolic_cap':3}

if __name__=='__main__':
    argparse.ArgumentParser(description=__doc__).parse_args()
    print(json.dumps(verify(),sort_keys=True,indent=2))
