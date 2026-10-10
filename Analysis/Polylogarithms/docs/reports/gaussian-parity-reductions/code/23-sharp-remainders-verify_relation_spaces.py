#!/usr/bin/env python3
"""Exact certificates for the restricted imaginary double relation spaces.

This checks formal rational linear algebra. It does not test period independence.
Requirements: sympy. Run from any directory; output is written beside this file.
"""
from __future__ import annotations
import json
import argparse
from math import comb
from pathlib import Path
import sympy as sp

X,Y=sp.symbols('X Y')

def canonical(level, r, s):
    r,s=r%level,s%level
    opposite=((-r)%level,(-s)%level)
    if (r,s)==opposite:
        return None,0
    return ((r,s),1) if (r,s)<opposite else (opposite,-1)

def make_presentation(level, weight):
    """Conjugation normalized; the g columns (1,0) are background."""
    colors=sorted({canonical(level,r,s)[0]
                   for r in range(level) for s in range(level)}-{None})
    keys=[(a,r,s) for a in range(1,weight) for r,s in colors
          if (r,s)!=(1,0)]
    ix={key:j for j,key in enumerate(keys)}
    def add_term(row, coeff, a, r, s):
        pair,sign=canonical(level,r,s)
        if sign and pair!=(1,0):
            row[ix[(a,*pair)]]+=sign*coeff
    rows=[]
    for p in range(1,weight):
        q=weight-p
        for r in range(level):
            for s in range(level):
                stuff=[0]*len(keys)
                add_term(stuff,1,p,r,s)
                add_term(stuff,1,q,s,r)
                shuffle=[0]*len(keys)
                for j in range(p):
                    add_term(shuffle,comb(q+j-1,j),q+j,s,r-s)
                for j in range(q):
                    add_term(shuffle,comb(p+j-1,j),p+j,r,s-r)
                rows.extend((stuff,shuffle))
    return sp.Matrix(rows),keys

def assignment(level, weight, A, keys):
    polynomials={(1,1):sp.Poly(A,X,Y)}
    if level==4:
        K=sp.expand(-A.subs({X:Y,Y:Y-X}, simultaneous=True))
        polynomials[(1,2)]=sp.Poly(K,X,Y)
        polynomials[(2,1)]=sp.Poly(-K.subs({X:Y,Y:X},simultaneous=True),X,Y)
    out=[]
    for a,r,s in keys:
        poly=polynomials.get((r,s))
        out.append(0 if poly is None else poly.coeff_monomial(X**(a-1)*Y**(weight-a-1)))
    return sp.Matrix(out)

def proved_basis(level, weight, keys):
    if weight%2==0:
        return []
    if level==4:
        expressions=[X**(a-1)*Y**(weight-a-1)-X**(weight-a-1)*Y**(a-1)
                     for a in range(1,(weight-1)//2+1)]
    elif weight<5:
        expressions=[]
    else:
        delta=X*Y*(X-Y)
        Q=X**2-X*Y+Y**2
        expressions=[delta**(2*b+1)*Q**((weight-5)//2-3*b)
                     for b in range((weight-5)//6+1)]
    return [assignment(level,weight,sp.expand(A),keys) for A in expressions]

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_name('relation_space_certificates.json'),
                        help='Destination JSON file (default: beside this script).')
    cli=parser.parse_args()
    checks=[]
    for level in (3,4):
        for weight in range(2,17):
            matrix,keys=make_presentation(level,weight)
            basis=proved_basis(level,weight,keys)
            expected=(weight+1)//6 if level==3 and weight%2 else (
                      (weight-1)//2 if level==4 and weight%2 else 0)
            nullity=len(matrix.nullspace())
            assert len(basis)==expected==nullity
            assert all(matrix*v==sp.zeros(matrix.rows,1) for v in basis)
            if basis:
                assert sp.Matrix.hstack(*basis).rank()==expected
            checks.append({'level':level,'weight':weight,'columns':len(keys),
                           'raw_rows':matrix.rows,'rank':len(keys)-nullity,
                           'nullity':nullity,'predicted_nullity':expected})
    matrix,keys=make_presentation(4,5)
    witness=assignment(4,5,(Y-X)**3,keys)
    assert matrix*witness==sp.zeros(matrix.rows,1)
    assert witness[keys.index((4,1,2))]==1
    entries=[{'a':a,'b':5-a,'first_color':r,'second_color':s,'value':int(v)}
             for (a,r,s),v in zip(keys,witness) if v]
    report={'claim_scope':'Restricted formal single-product depth-two relations; no period independence claim',
            'sympy_version':sp.__version__,'checks':checks,'weight_5_witness':entries,
            'original_S4_residual_functional_value':'1',
            'integer_normalized_A14_residual_functional_value':'161280'}
    destination=cli.output
    destination.parent.mkdir(parents=True,exist_ok=True)
    destination.write_text(json.dumps(report,indent=2)+'\n')
    print(f'Passed {len(checks)} exact rank/basis checks and the weight-five separating functional.')
    print(destination)

if __name__=='__main__':
    main()
