"""Exact polynomial-time small-step classification and rational certificates.

CLI: python code/classify.py input.json --output certificate.json
Input: {"hessians": [[[...], ...], ...], "weights": [1, 1, ...]}
Numbers may be integers or rational strings. Symmetry is checked. The algebraic
classification holds for any real symmetric Hessians; convexity is a separate
assumption for its optimization interpretation. Floats are deliberately rejected.
"""
from __future__ import annotations
import argparse
import json
from math import comb
from pathlib import Path
from typing import Any
import sympy as s
from fractions import Fraction as F
from exact_matrices import schedule_constants

def rational(x: Any) -> s.Rational:
    if isinstance(x,float) or isinstance(x,bool):
        raise ValueError("Use integers or rational strings, not floats/booleans")
    v=s.Rational(x)
    return v

def serialize(x):
    if isinstance(x,s.MatrixBase): return [[str(v) for v in row] for row in x.tolist()]
    if isinstance(x,(s.Rational,s.Integer,F)): return str(x)
    if isinstance(x,dict): return {k:serialize(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)): return [serialize(v) for v in x]
    return x

def classify(hessians,weights) -> dict:
    hs=[s.Matrix([[rational(v) for v in row] for row in a]) for a in hessians]
    if len(hs)<2: raise ValueError("At least two components are required")
    d=hs[0].rows;n=len(hs);m=len(weights)
    if d<1 or any(a.shape!=(d,d) or a!=a.T for a in hs):
        raise ValueError("Expected equal-size nonempty symmetric matrices")
    weights=[rational(a) for a in weights]
    if not 2<=m<=n or any(a<=0 for a in weights):
        raise ValueError("Require 2 <= m <= n and positive weights")
    z=s.zeros(d);h=sum(hs,z)/n;ds=[a-h for a in hs]
    v=sum((a*a for a in ds),s.zeros(d))/n
    basis=v.nullspace()
    Z=s.Matrix.hstack(*basis) if basis else s.zeros(d,0)
    P=Z*(Z.T*Z).inv()*Z.T if basis else s.zeros(d)
    constants={k:s.Rational(str(x)) for k,x in schedule_constants(tuple(F(str(a)) for a in weights),n).items()}
    c=constants['c'];gamma=constants['gamma'];t=constants['t']
    L=max(sum(abs(a[i,j]) for j in range(d)) for a in hs for i in range(d))
    Leff=max(weights)*L
    result=dict(n=n,m=m,dimension=d,mean=h,variance=v,kernel_basis=Z,
                kernel_projector=P,constants=constants,norm_upper_bound=L)
    if v==s.zeros(d):
        result.update(classification='identical',explanation='All components coincide; the two laws agree for every step size.')
        return result
    leakage=v*h*Z
    if leakage==s.zeros(d,Z.cols):
        vp=(v+P).inv()-P
        lam=1/s.trace(vp)
        eta0=min(1/(2*m*Leff),c*lam/(12*comb(2*m,3)*Leff**3))
        result.update(classification='eventual_domination',pseudoinverse=vp,
                      positive_eigenvalue_lower_bound=lam,step_threshold=eta0,
                      certificate='For 0 < eta <= threshold, Delta >= (c/2) eta^2 V.')
    else:
        index=next(j for j in range(Z.cols) if leakage[:,j]!=s.zeros(d,1))
        witness=Z[:,index];q=(witness.T*h*v*h*witness)[0]
        ratio=t/max(weights)
        C=(2*comb(2*m,3)*ratio**2 + 4*comb(2*m,4)*ratio
           +2*comb(2*m,4)*ratio**2 +6*comb(2*m,5)*(1+ratio)**2)
        eta0=min(1/(2*m*Leff),gamma*q/(2*C*Leff**5*(witness.T*witness)[0]))
        result.update(classification='eventual_reversal',kernel_witness=witness,
                      witness_linear_term=t*h*witness,leakage_energy=q,
                      remainder_constant=C,step_threshold=eta0,
                      certificate='x(eta)=v+eta*w obeys x^T Delta x <= -(gamma/2) q eta^4 for 0 < eta <= threshold.')
    return result

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path);parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    try:
        obj=json.loads(args.input.read_text())
        result=serialize(classify(obj['hessians'],obj['weights']))
        text=json.dumps(result,indent=2)+'\n'
        if args.output:
            args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(text)
        else: print(text,end='')
    except (ValueError,KeyError,TypeError,ZeroDivisionError) as exc:
        parser.exit(2,f'Invalid input: {exc}\n')
if __name__=='__main__': main()
