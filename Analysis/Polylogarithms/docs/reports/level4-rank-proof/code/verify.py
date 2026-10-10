#!/usr/bin/env python3
"""Regenerate exact certificates. Run from any working directory."""
from __future__ import annotations
import argparse, json, platform, time
from pathlib import Path
import numpy as np
import sympy as sp
import level4 as l

ROOT = Path(__file__).resolve().parents[1]
PRIME = 65521

def modular_rank(M: sp.Matrix, p: int = PRIME) -> tuple[int,list[int]]:
    """Deterministic finite-field elimination, not a probabilistic rank claim.

    p=65521 keeps each integer product below 2^32; int64 is ample.
    A nonzero modular minor is also a nonzero rational minor.
    """
    if M.cols == 0 or M.rows == 0:
        return 0, []
    A = np.array([[int(v)%p for v in row] for row in M.tolist()], dtype=np.int64)
    i, pivots = 0, []
    for j in range(M.cols):
        found = np.flatnonzero(A[i:,j])
        if not found.size:
            continue
        k = i+int(found[0])
        A[[i,k],:] = A[[k,i],:]
        A[i,j:] = A[i,j:]*pow(int(A[i,j]), -1, p)%p
        if i+1 < M.rows:
            A[i+1:,j:] = (A[i+1:,j:]-A[i+1:,j,None]*A[i,j:])%p
        pivots.append(j)
        i += 1
        if i == M.rows:
            break
    return i, pivots

def write_json(name: str, data) -> None:
    (ROOT/'data'/name).write_text(json.dumps(data, indent=2, default=lambda x: int(x) if isinstance(x, sp.Integer) else str(x))+'\n')

def run(rank_max: int, even_max: int) -> dict:
    if not __debug__:
        raise RuntimeError('Do not run verification with -O: assertions are required.')
    started = time.monotonic()
    census=[]
    for w in range(2,rank_max+1):
        M,K=l.matrix(w),l.kernel_basis(w)
        if M*K != sp.zeros(M.rows,K.cols):
            raise AssertionError(f'integer nullspace residual at weight {w}')
        kr,_=modular_rank(K)
        assert kr==K.cols
        rank,piv=modular_rank(M)
        cols=l.coordinates(w)
        keep=[i for i,c in enumerate(cols) if c[2:]!=(1,0)]
        Mg=M[:,keep]
        rg,pg=modular_rank(Mg)
        if w%2:
            m=(w-1)//2
            KC=K[keep,m:]
            assert Mg*KC==sp.zeros(Mg.rows,m)
            assert modular_rank(KC)[0]==m
            upper,upperg=M.cols-K.cols,Mg.cols-m
        else:
            upper,upperg=M.cols,Mg.cols
        assert (rank,rg)==(upper,upperg)==l.predicted_ranks(w)
        census.append(dict(weight=w,rows=M.rows,columns=M.cols,rank=rank,
                           nong_columns=Mg.cols,nong_rank=rg,nullity=K.cols,
                           prime=PRIME,pivot_columns=piv,nong_pivot_columns=pg,
                           integer_kernel_annihilation=True))
        if w%5==1 or w==rank_max:
            print(f'Exact rank certificate through weight {w}',flush=True)
    write_json('rank_certificates.json',census)
    formula_records=[]
    row_checks=0
    for w in range(2,even_max+1,2):
        values=l.even_values(w)
        for row in l.rows(w):
            residual=sp.expand(sum(c*v for c,v in zip(row.coefficients,values))-l.rhs(row))
            if residual != 0:
                raise AssertionError((w,row,residual))
            row_checks+=1
        for coordinate,value in zip(l.coordinates(w),values):
            formula_records.append(dict(weight=w,coordinate=coordinate,
                                        expression=str(value),latex=sp.latex(value)))
        print(f'All affine rows and formulas checked at weight {w}',flush=True)
    write_json('even_weight_identities.json',formula_records)
    # The odd affine compatibility is separate from the homogeneous rank proof.
    compatibility_checks=0
    for w in range(3,min(even_max+1,15)+1,2):
        t=l.affine_data(w)
        assert sp.expand(t['h']-t['b'])==0
        compatibility_checks+=1
    # Gaussian-only product rows must pass the kernel membership test.
    gaussian_tests=0
    for w in range(3,rank_max+1,2):
        for row in l.rows(w):
            if row.kind=='shuffle' and row.r==row.s==1:
                assert l.row_membership(w,list(row.coefficients))[0]
                gaussian_tests+=1
    # Explicit all-weight obstruction: C_0=Y^N-X^N, B=0.
    obstruction=[]
    for w in range(3,rank_max+1,2):
        cols=l.coordinates(w);m=(w-1)//2
        v=l.kernel_basis(w)[:,m]
        assert all(v[i]==0 for i,c in enumerate(cols) if c[2:]==(1,0))
        assert v[cols.index((w-1,1,1,2))]==1
        obstruction.append(dict(weight=w,p=w-1,pairing_with_S=1,
                                witness=[dict(coordinate=c,value=int(x))
                                         for c,x in zip(cols,v) if x]))
    write_json('S_even_obstructions.json',obstruction)
    cols=l.coordinates(5);M=l.matrix(5);K=l.kernel_basis(5)
    target=[0]*len(cols)
    for c,q in [((4,1,1,0),3),((3,2,1,0),3),((2,3,1,0),9),((4,1,1,2),7)]:
        target[cols.index(c)]=q
    witness=list(K[:,2])
    assert M*sp.Matrix(witness)==sp.zeros(M.rows,1)
    assert (sp.Matrix(1,len(cols),target)*sp.Matrix(witness))[0]==7
    write_json('weight5_certificate.json',dict(coordinates=cols,matrix=M.tolist(),
               kernel=K.tolist(),target=target,witness=witness,target_pairing=7))
    leading_records=[]
    for m in range(1,9):
        w=2*m
        pp=l.even_polynomials(w)
        C=(m-1)*l.beta(w)-l.LOG2*l.beta(w-1)/2-sum(
            (1-sp.Rational(2)**(1-2*k))*l.zeta(2*k)*l.beta(w-2*k) for k in range(1,m))
        E=m*l.beta(w)-l.LOG2*l.beta(w-1)/2-sum(
            l.zeta(2*k)*l.beta(w-2*k) for k in range(1,m))
        assert sp.expand(pp[1,1].subs({l.X:1,l.Y:0})-C)==0
        assert sp.expand(pp[1,3].subs({l.X:1,l.Y:0})-E)==0
        leading_records.append(dict(m=m,weight=w,C=str(sp.expand(C)),E=str(sp.expand(E))))
    write_json('leading_families.json',leading_records)
    # Independent rational rank at the central manuscript example.
    assert M.rank()==19 and M[:,[i for i,c in enumerate(cols) if c[2:]!=(1,0)]].rank()==17
    result=dict(status='PASS',rank_weights=len(census),rank_max=rank_max,
                odd_kernel_weights=sum(w%2 for w in range(2,rank_max+1)),
                even_formula_count=len(formula_records),affine_row_checks=row_checks,
                odd_affine_compatibility_checks=compatibility_checks,
                gaussian_membership_checks=gaussian_tests,
                odd_obstruction_weights=len(obstruction),
                weight5_target_pairing=7,leading_family_checks=2*len(leading_records),modular_prime=PRIME,
                python=platform.python_version(),sympy=sp.__version__,numpy=np.__version__,
                seconds=round(time.monotonic()-started,3))
    write_json('verification_report.json',result)
    return result

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rank-max',type=int,default=41)
    parser.add_argument('--even-max',type=int,default=12)
    args=parser.parse_args()
    if args.rank_max<5 or args.even_max<2 or args.even_max%2:
        parser.error('rank-max >= 5 and even even-max >= 2 are required')
    print(json.dumps(run(args.rank_max,args.even_max),indent=2))
