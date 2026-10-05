"""Finite marked-cycle / Poisson reconstruction through order two for A007716."""
import sympy as s
from math import factorial,gcd
from functools import lru_cache
from pathlib import Path
import json
w,t=s.symbols('w t',positive=True)
lambda_=w*w/2
beta=-w*w*(2*w*w+7*w+10)/(24*(1+w)**3)
b=w/(1+w);a=w/(2*(1+w)**2)
def L1(x):return x*a+x*x*b/2
def L2(x):return x*(beta-b*s.diff(beta,w))+x*x*(a-b*s.diff(a,w))/2-x**3*b*(s.diff(b,w)-1)/6

def normalized(m,s1,s2,order):
    l1=L1(s1)+L1(s2)-m*(m-1)/2
    if order==0:return s.Integer(1)
    if order==1:return l1
    l2=L2(s1)+L2(s2)-m*(m-1)*(2*m-1)/12
    return l2+l1*l1/2

@lru_cache(None)
def E(lens):
    if not lens:return 1
    total=0;r=len(lens)
    for subset in range(1<<(r-1)):
        block=(lens[0],)+tuple(lens[j+1] for j in range(r-1) if subset>>j&1)
        rest=tuple(lens[j+1] for j in range(r-1) if not subset>>j&1)
        g=0
        for x in block:g=gcd(g,x)
        weight=sum(d**(len(block)-1) for d in range(2,g+1) if g%d==0)
        total+=weight*E(rest)
    return total

def selections(m3,m4,limit):
    for b2 in range(limit+1):
        for b3 in range(min(m3,limit-b2)+1):
            for b4 in range(min(m4,limit-b2-b3)+1):
                lens=(2,)*b2+(3,)*b3+(4,)*b4
                choose=s.prod(t-j for j in range(b2))*s.Rational(1,factorial(b2))*s.binomial(m3,b3)*s.binomial(m4,b4)
                yield len(lens),E(lens)*choose

def poisson(poly):
    terms=s.Poly(s.expand(poly),t).terms();out=0
    for (j,),c in terms:
        # Direct recurrence for Poisson moments, no numerical fitting.
        moments=[s.Integer(1)]
        for k in range(j):moments.append(s.expand(lambda_*sum(s.binomial(k,l)*moments[l] for l in range(k+1))))
        out+=c*moments[j]
    return s.factor(out)
Q=[0,0,0];cases=0
for m3,m4 in [(0,0),(1,0),(2,0),(0,1)]:
    v=m3+2*m4;H=m3+m4;d=t+v+H;m=2*t+v+2*H
    sels=list(selections(m3,m4,2-v))
    for h,c1 in sels:
        for hp,c2 in sels:
            initial=v+h+hp
            if initial>2:continue
            factor=c1*c2*w**(2*v+2*H+h+hp)/(3**m3*factorial(m3)*4**m4*factorial(m4))
            for order in range(3-initial):
                Q[initial+order]+=poisson(factor*normalized(m,d+h,d+hp,order));cases+=1
Q=[s.factor(q) for q in Q]
if any(q.has(s.Float) for q in Q):raise RuntimeError('non-exact coefficient')
expected=w*w*(w**4+11*w**3+22*w*w+12*w-6)/(12*(1+w)**2)
if s.simplify(Q[0]-1) or s.simplify(Q[1]-expected):raise RuntimeError(('first coefficient',Q))
P1=s.factor(Q[1]+2*beta-s.Rational(1,12))
result={'status':'PASS','normalization':'a_n / [(B_n^2/n!) exp(W(n)^2/2)]','Q':[str(q) for q in Q],'explicit_carrier_first_correction':str(P1),'retained_contributions':cases,'method':'Exact marked cycle profiles, independent shore choices including overlaps, finite Poisson moments; no numerical fitting.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
