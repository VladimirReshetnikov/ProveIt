from __future__ import annotations
import argparse, itertools, json, platform, sys
from collections import Counter
from pathlib import Path
import sympy as sp
from mellin_exact import *


def run(output: Path):
    counts=Counter()
    def check(condition,category):
        if not condition: raise AssertionError(category)
        counts[category]+=1
    for W in range(2,11):
        for m in range(1,W):
            n=W-m
            for b in itertools.product((0,1),repeat=W-1):
                word=b+(1,)
                exact=0
                for positions in itertools.combinations(range(W),m):
                    p=set(positions)
                    other=set(range(W))-p
                    exact+=int(word[max(p)]==word[max(other)]==1)
                formula=sum(int(choose(j-1,m-1)+choose(j-1,n-1)) for j in range(1,W) if word[j-1])
                check(exact==formula,'shuffle_multiplicities')
    for W in range(2,15):
        for m in range(1,W):
            n=W-m
            check(sp.expand(jet(m,n)-compact(m,n))==0,'cone_to_compact')
            check(sp.expand(compact(m,n)-compact(n,m))==0,'symmetry')
    for N in range(1,10):
        for a in range(-1,N):
            R=sp.expand(t**(a-1)*(1-t)**(N-a-1))
            c,S,K=decompose(R)
            check(sp.cancel(R-c/t-sp.diff(S,t))==0,'kernel_decomposition')
            check(sp.cancel(S.subs(t,1))==0,'endpoint_anchoring')
            check(sp.cancel(t*(1-t)*K-S)==0,'kernel_transport')
            expected=0 if a>=1 else (-1)**(-a)*choose(N-a-1,-a)
            check(c==expected,'residue_coefficient')
    for d in range(10):
        # Bell recurrence is independent of the product coefficient evaluator.
        kappa={1:sp.harmonic(d)}
        for r in range(2,9):
            kappa[r]=sp.factorial(r-1)*((1+(-1)**r)*sp.zeta(r)+(-1)**(r+1)*sp.harmonic(d,r))
        bell={0:sp.Integer(1)}
        for h in range(9):
            if h:
                bell[h]=sp.expand(sum(choose(h-1,k-1)*kappa[k]*bell[h-k] for k in range(1,h+1)))
            check(sp.expand(beta_moment(d,h)-bell[h]/(d+1))==0,'beta_Bell_harmonics')
    for m in range(1,5):
        for n in range(1,5):
            for h in range(3):
                check(sp.expand(moment(1,-1,m,n,h)-jet(m,n,h,True))==0,'negative_resonance_recursion')
    y=sp.symbols('y')
    for n in range(2,17):
        check(sp.expand(sp.diff(inversion(n,y),y)-inversion(n-1,y))==0,'inversion_derivative')
        check(sp.expand(inversion(n,-y)-(-1)**n*inversion(n,y))==0,'inversion_parity')
    for W in range(2,12):
        for m in range(1,W):
            n=W-m
            for h in range(3):
                if (W+h)%2:
                    check(sp.expand(central(m,n,h)-central(n,m,h))==0,'central_symmetry')
    check(low(jet(2,1))==17*sp.zeta(4)/4,'printed_examples')
    check(sp.expand(low(jet(3,1))-(sp.Rational(11,2)*sp.zeta(5)+sp.zeta(2)*sp.zeta(3)))==0,'printed_examples')
    check(sp.expand(low(jet(2,2))-(2*sp.zeta(5)+4*sp.zeta(2)*sp.zeta(3)))==0,'printed_examples')
    # A changed coefficient must be rejected without transcendental numerics.
    check(sp.expand(jet(3,2)-(compact(3,2)+Z(2,4)))!=0,'corruption_control')
    record={'status':'PASS','python':platform.python_version(),'sympy':sp.__version__,
            'checks':dict(counts),'total_checks':sum(counts.values()),
            'scope':'Finite exact identities only; analytic proofs are in the article.'}
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record,indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser(); p.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'data/exact_results.json')
    run(p.parse_args().output)
