#!/usr/bin/env python3
"""Exact checks of the polynomial kernel parametrization (no rank inference)."""
from pathlib import Path
import sys, json
from math import comb
import sympy as sp
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT/'upstream'))
from package_io import read_json
from full_ds import system
X,Y=sp.symbols('X Y')

def kernel_basis(w):
    n=w-2
    if not w%2 or w<3:
        raise ValueError('odd weight >=3 required')
    keys,A,rhs,labels=system(w)
    columns=[]
    descriptors=[]
    for sector in ('G','D'):
        for j in range(n+1):
            if j%2 != (sector=='G'): continue
            p=X**(n-j)*(2*Y-X)**j
            g=p if sector=='G' else sp.S.Zero
            d=p if sector=='D' else sp.S.Zero
            polys={
                (0,1):-g.xreplace({X:Y,Y:X}),
                (1,0):g,
                (1,1):-d.xreplace({X:X-Y,Y:X}),
                (1,2):d,
                (1,3):g.xreplace({X:X-Y,Y:X}),
                (2,1):-d.xreplace({X:Y,Y:X}),
            }
            polys={k:sp.Poly(v,X,Y) for k,v in polys.items()}
            column=sp.Matrix([polys[(r,s)].coeff_monomial(X**(a-1)*Y**(b-1)) for a,b,r,s in keys])
            assert A*column==sp.zeros(A.rows,1), (w,sector,j)
            columns.append(column)
            descriptors.append([sector,j])
    K=sp.Matrix.hstack(*columns)
    assert K.rank()==w-1
    ng=[i for i,key in enumerate(keys) if key[2:] != (1,0)]
    rg=A.rank()
    rng=A[:,ng].rank()
    assert rg==5*w-6, (w,rg)
    assert rng==(9*w-11)//2, (w,rng)
    return dict(weight=w,rows=A.rows,columns=A.cols,rank=rg,rank_without_g=rng,
                kernel_basis_rank=K.rank(),kernel_descriptors=descriptors,
                verified_matrix_times_basis_zero=True)

def verify(weights=None):
    default_weights = list(range(3, 14, 2))
    weights = default_weights if weights is None else list(weights)
    results=[]
    for w in weights:
        result=kernel_basis(w)
        print(json.dumps(result),flush=True)
        results.append(result)
    if weights == default_weights:
        assert results == read_json('rank_parametrization_receipt.json'), 'Rank reference receipt changed'
    return results

if __name__=='__main__':
    verify(list(map(int,sys.argv[1:])) or None)
