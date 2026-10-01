#!/usr/bin/env python3
"""Independent finite checks of the Poisson identity and ADE coefficients."""
from __future__ import annotations
import json, math, time
from fractions import Fraction as Q
from pathlib import Path
import mpmath as mp
import networkx as nx
import sympy as sp
from verify import coeff, exact_histogram, cayley, numeric, ade_shape

ROOT=Path(__file__).resolve().parents[1]

def R(n:int,k:int)->Q:
    return sum((Q(math.perm(n-k,j),n**j)*math.comb(k+j-2,k-2)*(k+j)
                for j in range(n-k+1)),Q(0))/n**(k-1)

def poisson_formula_exact(n:int,p:Q)->Q:
    """Use exp(nq)P(Poisson(nq)<=n-2) as its finite exponential sum."""
    q=1-p;c=Q(9,8);B=Q(math.factorial(n),cayley(n))
    out=q**n+n*p*q**(n-1)
    out+=c*p**3*B*sum(((n*q)**i/math.factorial(i) for i in range(n-1)),Q(0))
    out+=c*p*p*n*(n-1)*q**(n-1)
    for k in range(2,min(9,n)+1):
        out+=(coeff(k)-c)*math.perm(n,k)*p**k*q**(n-k)*R(n,k)
    return out

def main():
    start=time.time();checks=0
    for n in range(2,36):
        hist=exact_histogram(n)
        for p in [Q(1,100),Q(1,5),Q(1,2),Q(4,5),Q(99,100)]:
            exact=sum((count*p**k*(1-p)**(n-k) for (k,l),count in hist.items()),Q(0))/cayley(n)
            assert exact==poisson_formula_exact(n,p),(n,p)
            checks+=1
    rows=[];trees_checked=0
    for n in range(2,12):
        total=Q(0);passed=0
        for tree in nx.nonisomorphic_trees(n):
            adj={v:set(tree.neighbors(v)) for v in tree}
            shape=ade_shape(adj)
            # PSD test by exact eigenvalue-sign equivalent: all coefficients
            # of det(tI + 2I - A) must be nonnegative (all roots are real).
            A=sp.Matrix(nx.to_numpy_array(tree,dtype=int).tolist())
            poly=(2*sp.eye(n)-A).charpoly().all_coeffs()
            # charpoly is det(tI-M); alternate signs give det(tI+M).
            psd=all(((-1)**i)*v>=0 for i,v in enumerate(poly))
            assert psd==(shape is not None),(n,shape,poly)
            trees_checked+=1
            if shape is not None:
                aut=sum(1 for _ in nx.algorithms.isomorphism.GraphMatcher(tree,tree).isomorphisms_iter())
                total+=Q(1,aut);passed+=1
        assert total==coeff(n),(n,total,coeff(n))
        rows.append({'n':n,'stable_unlabeled_skeletons':passed,'sum_inverse_automorphisms':str(total)})
    s,t,p=sp.symbols('s t p',real=True);q=1-p
    den=q+p*sp.exp(s)
    L=t+sp.log(den)+q*sp.exp(-t)/den-q
    logC=2*(sp.log(p)+s-sp.log(den))+sp.log(1-q*sp.exp(-t)/den)
    at=lambda f:sp.simplify(f.subs({s:0,t:0}))
    assert at(sp.diff(L,s))==p**2
    assert at(sp.diff(L,t))==p
    assert sp.simplify(at(sp.diff(L,s,2))-2*p*p*q)==0
    assert sp.simplify(at(sp.diff(L,s,t))-p*q)==0
    assert at(sp.diff(L,t,2))==q
    assert sp.simplify(at(sp.diff(logC,s))-3*q)==0
    assert sp.simplify(at(sp.diff(logC,t))-q/p)==0
    assert sp.simplify(at(sp.diff(logC,s,2))+3*p*q)==0
    assert sp.simplify(at(sp.diff(logC,s,t))+q/p)==0
    assert sp.simplify(at(sp.diff(logC,t,2))+q/p**2)==0
    report={'status':'PASS','exact_poisson_identity_checks':checks,
            'nonisomorphic_trees_spectral_and_shape_checked':trees_checked,
            'symbolic_cumulant_checks':10,'skeleton_rows':rows,
            'seconds':round(time.time()-start,3),
            'scope':'Finite identities and exact PSD signs only; not a proof-assistant formalization.'}
    (ROOT/'data'/'extra_checks.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
