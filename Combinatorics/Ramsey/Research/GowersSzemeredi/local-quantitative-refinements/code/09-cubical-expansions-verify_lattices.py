#!/usr/bin/env python3
"""Exhaustive exact lattice census in dimensions 3 and 4.
Requires SymPy. Writes lattice_results.json beside this script.
No floating-point arithmetic or heuristic rank tests are used.
"""
import collections
import itertools as it
import json
import math
from pathlib import Path
import sympy as s
from sympy.matrices.normalforms import smith_normal_form
from sympy.polys.domains import ZZ
from verify_expansion import coeffs

def census(d, size):
    vertices=list(it.product((0,1),repeat=d))
    counts=collections.Counter()
    for inds in it.combinations(range(2**d),size):
        A=s.Matrix([[1]*size]+[[vertices[i][j] for i in inds] for j in range(d)])
        D=smith_normal_form(A,domain=ZZ)
        inv=tuple(abs(int(D[i,i])) for i in range(min(D.shape)) if D[i,i])
        rank=len(inv)
        if rank==size:
            name=f'independent-index-{math.prod(inv)}'
        else:
            ns=A.nullspace()
            assert len(ns)==1
            v=ns[0]
            name='full-support-circuit' if all(v) else 'coloop'
        counts[(name,inv)]+=1
    P,T,Q,S=coeffs(d)
    if size==4:
        assert counts[('full-support-circuit',(1,1,1))]==P
        assert counts[('independent-index-2',(1,1,1,2))]==T
    else:
        assert counts[('full-support-circuit',(1,1,1,1))]==Q
        assert counts[('independent-index-3',(1,1,1,1,3))]==S
    assert sum(counts.values())==math.comb(2**d,size)
    return [{'type':name,'invariant_factors':inv,'count':n}
            for (name,inv),n in sorted(counts.items())]

def main():
    out={'sympy_version':s.__version__,'censuses':{}}
    for d in (3,4):
        for size in (4,5):
            out['censuses'][f'd={d},size={size}']=census(d,size)
            print(f'd={d}, size={size} passed',flush=True)
    B=s.Matrix([[1,0,1,1,1],[0,1,1,0,0],[0,1,0,1,1],
                [1,1,0,0,1],[1,1,0,1,0]])
    A=s.ones(1,6).col_join(s.zeros(5,1).row_join(B))
    r=s.Matrix([2,1,3,2,1,1])
    assert B.det()==-5
    assert all(int(v)%5==0 for v in A*r)
    assert all(int(v)%5!=0 for v in r)
    D=smith_normal_form(A,domain=ZZ)
    assert [abs(int(D[i,i])) for i in range(6)]==[1,1,1,1,1,5]
    out['five_torsion_certificate']={'B':B.tolist(),'det_B':-5,
                                     'kernel_mod_5':list(r),'A_times_r':list(A*r),
                                     'smith_invariants':[1,1,1,1,1,5]}
    out['all_passed']=True
    dest=Path(__file__).with_name('lattice_results.json')
    dest.write_text(json.dumps(out,indent=2,default=int)+'\n')
    print(dest)

if __name__=='__main__':
    main()
