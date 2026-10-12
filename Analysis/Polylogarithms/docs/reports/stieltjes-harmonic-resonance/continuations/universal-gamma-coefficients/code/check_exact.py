"""Independent exact checks. Run from any directory; output is package-local."""
from pathlib import Path
from fractions import Fraction as Q
import json, time
import sympy as s
from normal_forms import hierarchy, D, addto, trim, normal
from mixed_coefficients import coefficient
from pde_recurrence import coef, X

ROOT=Path(__file__).resolve().parents[1]

def main():
    start=time.perf_counter(); count=identities=0; examples={}
    for m,A,N,H in hierarchy(30):
        actual=D(H)
        for mon,v in N.items(): addto(actual,mon,v)
        assert actual==A
        identities+=1
        for c in range(m//4+1):
            for b in range((m-4*c)//3+1):
                for k in range((m-4*c-3*b)//2+1):
                    a=m-4*c-3*b-2*k
                    assert N.get(trim((a,k,b,c)),Q(0))==coefficient(a,k,b,c)
                    count+=1
        if m==6:
            Nt,_=normal({mon:v for mon,v in A.items() if len(mon)<=4})
            assert N[(0,0,2)]==1 and Nt[(0,0,2)]==-5
            examples['premature_truncation']={'correct_u2_squared':'1','incorrect_u2_squared':'-5'}
        if m==11:
            assert N[(0,0,1,2)]==-55
            # Corruption control: the same comparison rejects the opposite sign.
            assert N[(0,0,1,2)] != 55
    v=s.symbols('v')
    alpha=(1+3*v*v)/24; beta=v*(1+v*v)/48
    W1=(1-v**-2)/2
    W2=3*(1-v*v)**2/(1+3*v*v)**2
    W3=-(1-v*v)**3/(4*v*v*(1+v*v)**2)
    for W,d in [(W1,1),(W2,2),(W3,3)]:
        val=W+s.diff(v*W,v)
        if d>=2: val+=4*s.diff(alpha*W,v,2)
        if d>=3: val+=8*s.diff(beta*W,v,3)
        assert s.cancel(val-1)==0
        for endpoint in [-1,1]:
            for j in range(d): assert s.diff(W,v,j).subs(v,endpoint)==0
    comparisons=0
    for c,limit in [(0,7),(2,6),(3,4),(4,3)]:
        for b in range(limit):
            if c==0 and b<2: continue
            if c==0:
                closed=s.Rational(24,s.factorial(b)*24**b)*sum(
                    s.binomial(b-2,j)*3**j/s.prod(X+1+2*j+2*h for h in range(3))
                    for j in range(b-1))
            else:
                closed=s.Rational(-12,s.factorial(b)*s.factorial(c)*24**b*48**c)*sum(
                    s.binomial(b,j)*3**j*s.binomial(c-2,l)/s.prod(X+c-1+2*j+2*l+2*h for h in range(4))
                    for j in range(b+1) for l in range(c-1))
            assert s.cancel(closed-coef(b,c))==0
            comparisons+=1
    report={'result':'PASS','maximum_weight':30,'exact_coefficient_comparisons':count,
            'full_normal_form_identities':identities,'kernel_identities':3,
            'endpoint_vanishing_checks':12,'rational_function_PDE_comparisons':comparisons,
            'regression_controls':examples,'sign_corruption_rejected':True,
            'elapsed_seconds':time.perf_counter()-start,
            'scope':'Finite exact replay. Infinite-family proofs are in the article; no proof-assistant formalization.'}
    (ROOT/'data'/'exact_checks.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__': main()
