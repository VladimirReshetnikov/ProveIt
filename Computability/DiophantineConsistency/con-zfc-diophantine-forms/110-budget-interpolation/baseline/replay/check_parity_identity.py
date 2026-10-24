#!/usr/bin/env python3
"""Independent resultant derivation; imports no upstream builder or auditor."""
import argparse
import json
from pathlib import Path
import sympy as s

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path(__file__).resolve().parent/'results/PARITY_IDENTITY.json')
    args = parser.parse_args()
    x,A,B,C,u,v = s.symbols('x A B C u v')
    # Eliminate the roots of 4B and A successively from the norm of 4 sqrt(C).
    two = s.resultant((x+u)**2-16*C,u**2-4*B,u)
    three = s.resultant(two.subs(x,x+v),v**2-A,v)
    a,b,t = s.symbols('a b t')
    oddx = 2*t+1
    oddA = 4*a+1
    oddB = 4*b+1
    U = t*(t+1)-a-oddB+4*C
    M = U**2+4*oddx**2*C-oddA*oddB
    N = M**2-16*oddx**2*U**2*C
    difference = s.Poly(s.expand(three.subs({x:oddx,A:oddA,B:oddB})-256*N),a,b,C,t)
    if not difference.is_zero:
        raise ValueError('Primitive three-root norm identity failed')
    # Also verify the equivalent expression printed for circuit comparison.
    n = t*(t+1)-a-oddB-4*C
    alternative = (n**2-oddA*oddB-4*oddA*C-16*oddB*C)**2-16*oddA*oddB*C*oddx**2
    if s.expand(N-alternative)!=0:
        raise ValueError('Alternative primitive expression failed')
    receipt={'status':'PASS','method':'Two independent exact resultants, followed by free integer-polynomial expansion.',
             'upstream_code_imported':False,'sympy':s.__version__,
             'identity':'F3(2t+1;4a+1,4(4b+1),16C)=256 N',
             'alternative_primitive_identity':True,
             'generic_norm_terms':len(s.Poly(three,x,A,B,C).terms()),
             'primitive_norm_terms':len(s.Poly(s.expand(N),a,b,C,t).terms()),
             'scope':'Universal local integer-polynomial identities only, not the inherited calibration or complete15-variable degree certificate.'}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt))
if __name__=='__main__':
    main()
