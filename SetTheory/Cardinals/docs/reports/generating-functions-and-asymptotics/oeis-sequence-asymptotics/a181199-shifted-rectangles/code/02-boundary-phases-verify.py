"""Reproduce finite exact checks. These are diagnostics, not proofs of theorems."""
from __future__ import annotations
import csv, json, time
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from math import comb, factorial, prod
from pathlib import Path
from tableaux import (count, bitmask_count, chamber, chamber_dp, event_counts,
                      dyck_words, height, hook, rare_core)

ROOT=Path(__file__).resolve().parents[1]

def main():
    start=time.perf_counter(); checks=Counter()
    def check(category, condition, detail):
        if not condition: raise AssertionError((category,detail))
        checks[category]+=1
    # A wholly separate ideal-of-poset implementation.
    for m in range(1,5):
        for n in range(1,5):
            for rare in ([False,True] if m>=2 else [False]):
                check('independent poset enumeration',count(m,n,rare)==bitmask_count(m,n,rare),(m,n,rare))
    for r in range(5):
        points=[tuple(reversed(c)) for c in combinations(range(1,7),r)]
        for u in points:
            for v in points:
                check('reflection kernel',chamber(u,v)==chamber_dp(u,v),(u,v))
    for m in range(1,6):
        for n in range(2,7):
            ev=event_counts(m,n)
            check('event decomposition',sum(ev.values())==count(m,n),(m,n))
            for w in dyck_words(m):
                check('event realizability', (ev.get(w,0)>0)==(height(w)<=n-1),(m,n,w))
                dual=w[::-1].translate(str.maketrans('BD','DB'))
                check('rotation duality',ev.get(w,0)==ev.get(dual,0),(m,n,w))
            if m>=2:
                rare=sum(v for w,v in ev.items() if w!='B'*m+'D'*m)
                check('rare event-word sum',rare==count(m,n,True),(m,n))
    check('worked event example',event_counts(3,4)=={
        'BBBDDD':4,'BBDBDD':16,'BBDDBD':4,'BDBBDD':4,'BDBDBD':1},'m=3,n=4')
    oeis={4:[1,1,8,169,6392,352184,25097600,2152061145,212012802584,23263015359672],
          5:[1,1,16,985,141696,36372976,14083834704,7372392431849,
             4848332563899256,3808369342900073856]}
    for m,terms in oeis.items():
        for n,value in enumerate(terms,1):
            check('OEIS reference values',count(m,n)==value,(m,n))
    rows=[]
    for m in range(2,6):
        for n in range(2,21):
            R=count(m,n,True); H=rare_core(m,n)
            M=factorial(m*n)//factorial(n)**m
            check('core lower bound',H<=R,(m,n))
            check('two-row separation bound',R*comb(2*n,n)<=M,(m,n))
            check('core error bound',R==H if m==2 else (R-H)*comb(3*n,n)<=M,(m,n))
            rows.append({'m':m,'n':n,'R':R,'H':H,'M':M})
    # Classical small-width controls; not claimed as new formulas.
    for m in range(1,9):
        check('classical controls',count(m,2)==1,(m,2))
        check('classical controls',count(m,3)==2**(m-1),(m,3))
    for n in range(1,25):
        check('classical controls',count(2,n)==comb(2*n-2,n-1)//n,('Catalan',n))
        check('classical controls',count(2,n,True)==1,('rare height two',n))
    # The rational-moment coefficient engine is independent of the enumerators.
    from coefficients import rare_coefficients, moments
    import sympy as s
    for m in range(2,6):
        r=m-2
        actual=rare_coefficients(m,1)
        expected=s.Rational(r*(6*r**3-52*r**2-268*r-283),72*(r+2))
        check('universal first correction',actual==[1,expected],m)
    for m in (3,4,5):
        saved=json.loads((ROOT/f'data/coefficients_m{m}.json').read_text())
        actual=[str(v) for v in rare_coefficients(m,3)]
        check('saved all-order coefficients',actual==saved['b'],m)
    # Exact Gaussian-limit moments for the common-mode covariance matrix:
    # Y_i=Z_i+V, Var Z_i=1 and Var V=1/2.
    for powers, expected in [((1,),0),((2,),s.Rational(3,2)),
                             ((1,1),s.Rational(1,2)),((4,),s.Rational(27,4)),
                             ((2,2),s.Rational(11,4)),((3,1),s.Rational(9,4))]:
        check('common-mode limiting moments',moments(powers,0)[0]==expected,powers)
    # Verify a few exact beta-binomial moments by direct rational summation
    # against their asymptotic-series engine (independent finite value formula).
    N=s.Symbol('N'); z=s.Symbol('z')
    # Univariate raw identities derived without the centered-moment implementation.
    for k in range(1,5):
        expr=s.ff(N,k)*s.rf(N,k)/s.rf(2*N+1,k)
        for n in range(2,9):
            weighted=Fraction(0)
            for x in range(n+1):
                # Beta-binomial distribution with alpha=n,beta=n+1.
                mass=Fraction(comb(n,x)*prod(range(n,n+x))*prod(range(n+1,n+1+n-x)),
                              prod(range(2*n+1,3*n+1)))
                weighted+=mass*(prod(range(x-k+1,x+1)) if x>=k else 0)
            val=expr.subs(N,n)
            check('exact beta factorial moments',weighted==Fraction(int(s.numer(val)),int(s.denom(val))),(k,n))
    out={'status':'PASS','checks':dict(checks),'total_checks':sum(checks.values()),
         'seconds':round(time.perf_counter()-start,3),
         'meaning':'Finite exact checks; not peer review, formal verification, or a proof of an infinite claim.'}
    ROOT.joinpath('data').mkdir(exist_ok=True)
    (ROOT/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n')
    with (ROOT/'data/exact_rare_counts.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=rows[0].keys());writer.writeheader();writer.writerows(rows)
    text='\n'.join(f'PASS: {k}: {v} checks' for k,v in checks.items())
    text+=f'\nTOTAL: {sum(checks.values())} exact checks; {out["seconds"]} seconds\n'
    text+='These finite checks corroborate, but do not replace, the proofs in article.tex.\n'
    (ROOT/'data/verification.txt').write_text(text)
    print(text,end='')

if __name__=='__main__': main()
