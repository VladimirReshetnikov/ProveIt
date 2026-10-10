#!/usr/bin/env python3
"""Exact, reproducible checks for integral distribution research results.

Usage: python verify_integral_distribution.py
Requires Python 3.10+, sympy and mpmath. Writes verification_report.json.
The proofs are in ../../sections/05-integral-distribution.tex;
checks corroborate them.
"""
from __future__ import annotations
from itertools import combinations, product
from math import gcd
from pathlib import Path
import json
import platform
import sympy as sp
import mpmath as mp
from sympy.matrices.normalforms import smith_normal_form
from integral_distribution import Distribution


def signature(A):
    S=smith_normal_form(A,domain=sp.ZZ)
    diagonal=[abs(int(S[i,i])) for i in range(min(S.shape))]
    if S.rows > S.cols:
        diagonal.extend([0]*(S.rows-S.cols))
    return sorted(d for d in diagonal if d!=1)


def rank_mod(A, ell):
    rows=[[int(v)%ell for v in row] for row in A.tolist()]
    if not rows or not rows[0]:
        return 0
    r=0
    for col in range(len(rows[0])):
        pivot=next((j for j in range(r,len(rows)) if rows[j][col]),None)
        if pivot is None:
            continue
        rows[r],rows[pivot]=rows[pivot],rows[r]
        inverse=pow(rows[r][col],-1,ell)
        rows[r]=[x*inverse%ell for x in rows[r]]
        for j in range(r+1,len(rows)):
            c=rows[j][col]
            if c:
                rows[j]=[(x-c*y)%ell for x,y in zip(rows[j],rows[r])]
        r+=1
        if r==len(rows):
            break
    return r


def core_prediction(p, ell, a, b):
    hp=int(sp.n_order(ell,p)) if p>2 else 1
    hl=int(sp.n_order(p,ell)) if ell>2 else 1
    cp=(p-1)//hp
    cl=(ell-1)//hl
    Sp=sum(b**j for j in range(hp))
    Sl=sum(a**j for j in range(hl))
    Dp=b**hp-1
    Dl=a**hl-1
    blocks=[sp.Matrix([[Dp]]) for _ in range(cp-1)]
    blocks += [sp.Matrix([[Dl]]) for _ in range(cl-1)]
    blocks += [sp.Matrix([[(a-1)*(b-1),0,0],[-(a-1),Sp,0],[-(b-1),0,Sl]])]
    return sp.diag(*blocks)


def resolution(q, weights):
    primes=tuple(sorted(map(int,sp.factorint(q))))
    groups=[]
    for degree in range(len(primes)+1):
        basis=[]
        for S in combinations(primes,degree):
            d=sp.prod(S)
            basis.extend((S,int(r)) for r in range(0,q,int(d)))
        groups.append(basis)
    maps=[]
    for degree in range(1,len(groups)):
        target={x:i for i,x in enumerate(groups[degree-1])}
        mat=sp.zeros(len(target),len(groups[degree]))
        for col,(S,x) in enumerate(groups[degree]):
            for j,p in enumerate(S):
                T=tuple(u for u in S if u!=p)
                step=int(sp.prod(T))
                sign=(-1)**j
                for y in range(0,q,step):
                    if (p*y-x)%q==0:
                        mat[target[T,y],col] += sign
                mat[target[T,x],col] -= sign*weights[p]
        maps.append(mat)
    return groups,maps


def main():
    report={'python':platform.python_version(),'sympy':sp.__version__,
            'mpmath':mp.__version__,'checks':{},'examples':{}}
    symbolic=[]
    for q in range(2,61):
        D=Distribution(q)
        C=D.normal_matrix()
        assert len(D.basis)==int(sp.totient(q))
        assert all(sp.expand(x)==0 for x in C*D.relation_matrix().T)
        basis_columns=[D.to_residue(x) for x in D.basis]
        assert C[:,basis_columns]==sp.eye(len(D.basis))
        # Meaningful independent bound: actual polynomial supports obey the theorem.
        for col in range(q):
            for c in C[:,col]:
                polynomial=sp.Poly(c,*D.weights)
                assert all(polynomial.degree(t)<=e for t,(_,e) in zip(D.weights,D.factors))
        symbolic.append(q)
    report['checks']['symbolic_normal_forms']={'q':symbolic,'all_relation_residuals':0,
            'basis_submatrices':'identity','per_prime_degree_bounds':'passed'}
    print('Exact normal-form identities verified for q=2..60.',flush=True)

    determinant_levels=(2,3,4,5,6,8,9,10,12,15,16,18,20,21,24,25,27,30,35)
    determinants=[]
    for q in determinant_levels:
        D=Distribution(q)
        det=sp.factor(D.primitive_matrix().det(method='domain-ge'))
        quotient=sp.cancel(det/D.determinant_formula())
        assert quotient in (-1,1)
        determinants.append({'q':q,'orientation_sign':int(quotient)})
    report['checks']['integral_primitive_determinants']=determinants
    print('Integral determinant formulas verified at 19 levels.',flush=True)

    syzygies=[]
    for q in (6,12,15,21,30,60,105):
        primes=tuple(sorted(map(int,sp.factorint(q))))
        for style in ('zero','one','prime','prime_plus_one'):
            weights={p:{'zero':0,'one':1,'prime':p,'prime_plus_one':p+1}[style] for p in primes}
            groups,maps=resolution(q,weights)
            assert all(not any(A*B) for A,B in zip(maps,maps[1:]))
            for char in (2,3,5,7):
                previous=0
                ranks=[]
                for j,A in enumerate(maps):
                    rank=rank_mod(A,char)
                    target=(q-int(sp.totient(q))) if j==0 else len(groups[j])-previous
                    assert rank==target,(q,style,char,j,rank,target)
                    previous=rank
                    ranks.append(rank)
                assert ranks[-1]==len(groups[-1])
                syzygies.append({'q':q,'weights':style,'characteristic':char,'ranks':ranks})
    report['checks']['finite_characteristic_resolutions']=syzygies
    print('112 finite-characteristic resolution checks passed.',flush=True)

    semiprimes=[]
    primes=(2,3,5,7,11,13)
    choices=(-2,-1,0,1,2,3)
    for p,ell in combinations(primes,2):
        if p*ell>105:
            continue
        D=Distribution(p*ell)
        P=D.primitive_matrix()
        for a,b in product(choices,repeat=2):
            actual=P.subs({D.weights[0]:a,D.weights[1]:b})
            prediction=core_prediction(p,ell,a,b)
            assert signature(actual)==signature(prediction),(p,ell,a,b,signature(actual),signature(prediction))
        semiprimes.append(p*ell)
    report['checks']['two_prime_core']={'levels':semiprimes,
            'weights_each_prime':choices,'specializations':len(semiprimes)*len(choices)**2,
            'checked':'complete integer Smith signature including zeros'}
    print(f'Two-prime core verified at {len(semiprimes)*len(choices)**2} exact integer specializations.',flush=True)

    for q,k in ((6,5),(12,1),(15,1),(15,2)):
        D=Distribution(q)
        substitutions={t:p**k for p,t in zip(D.primes,D.weights)}
        P=D.primitive_matrix().subs(substitutions)
        extension=P.inv()*D.normal_matrix().subs(substitutions)
        common=int(sp.ilcm(*(sp.denom(x) for x in extension)))
        primitive=[r for r in range(q) if gcd(r,q)==1]
        example={'q':q,'s':k,'integral_basis_residues':[D.to_residue(x) for x in D.basis],
                 'primitive_residues':primitive,'index':abs(int(P.det())),
                 'nonunit_smith_signature':signature(P),'exact_common_denominator':common}
        if q==15 and k==2:
            assert common==511680
            assert list(extension[:,3]) == [sp.Rational(n,6560) for n in (729,81,9,81,1,729,1,9)]
            assert list(extension[:,5]) == [sp.Rational(n,624) for n in (25,1,25,25,1,1,25,1)]
            assert list(extension[:,0]) == [sp.Rational(1,192)]*8
            example['zeta_2_one_fifth_coefficients']=[str(x) for x in extension[:,3]]
            example['zeta_2_one_third_coefficients']=[str(x) for x in extension[:,5]]
            example['zeta_2_endpoint_coefficients']=[str(x) for x in extension[:,0]]
            mp.mp.dps=90
            values=[mp.zeta(2,mp.mpf(r)/q) for r in primitive]
            errors=[]
            for r in (0,3,5):
                rhs=sum(mp.mpf(str(c.p))/mp.mpf(str(c.q))*v for c,v in zip(extension[:,r],values))
                lhs=mp.zeta(2,mp.mpf(r)/q if r else 1)
                error=abs(lhs-rhs)
                errors.append(mp.nstr(error,8))
                assert error < mp.mpf('1e-85')
            example['independent_hurwitz_numeric_errors_at_90_digits']=errors
        report['examples'][f'q{q}_s{k}']=example

    out=Path(__file__).with_name('verification_report.json')
    out.write_text(json.dumps(report,indent=2)+'\n')
    summary={
        'symbolic_grid_levels':len(symbolic),
        'symbolic_grid_range':[min(symbolic),max(symbolic)],
        'integral_determinant_levels':len(determinants),
        'finite_characteristic_resolution_checks':len(syzygies),
        'complete_two_prime_smith_checks':len(semiprimes)*len(choices)**2,
        'all_checks_passed':True,
        'examples':report['examples'],
    }
    Path(__file__).with_name('verification_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print('Wrote',out,flush=True)

if __name__=='__main__':
    main()
