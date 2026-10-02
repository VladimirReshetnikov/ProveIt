#!/usr/bin/env python3
"""Fresh finite diagnostics for the fine addendum; no claim of analytic proof."""
from collections import Counter
from fractions import Fraction
from functools import cache
from pathlib import Path
import hashlib, json, math
import mpmath as mp
import sympy as sp

HERE = Path(__file__).resolve().parent
RESEARCH = HERE.parent / 'support' / 'fine-research'

def children(x):
    s,u,k = x
    out=[]
    for i in range(s+u):
        if i<s:
            out.append((s-1,u if i<k else u+1,i))
        elif i<k:
            out.append((s+1,u-1,i+1))
        else:
            out.append((s+1,u,i+1))
    return out

def h(s,y,R): return y if y<=s else s+R*(y-s)
def rank(x,R):
    s,u,k=x
    return h(s,k,R)/(s+R*u)
def pad(x,L): return x[0]+L,x[1],x[2]+L

states=[(s,m-s,k) for m in range(1,21) for s in range(m) for k in range(m)]
padchecks=0
for x in states:
    s,u,k=x; m=s+u
    cs=children(x)
    assert all(a>=0 and b>=1 and 0<=c<a+b for a,b,c in cs)
    assert sum(a+b for a,b,c in cs)==m*m+u-k
    assert sum(a for a,b,c in cs)==m*s+m-2*s
    assert sum(c for a,b,c in cs)==m*(m+1)//2-s
    assert sum((a+b)**2 for a,b,c in cs)==m**3+2*m*(m-s-k)+m-abs(s-k)
    for L in (0,1,3,11):
        assert children(pad(x,L))[L:]==[pad(y,L) for y in cs]
        padchecks += m

# Independent frozen integration, preserving each integer breakpoint.
qs=[1e-6,.03,.3,1.,3.,10.,30.,80.,200.]
residual_checks=0
worst_upper=worst_lower=0.0
for q in qs:
    R=2-math.exp(-q)
    p=(q+math.log(R))/2
    bnorm=math.sqrt(R)*(-math.expm1(-q))/q # b / exp(q/2)
    for x in states:
        s,u,k=x; m=s+u; D=s+R*u; r=rank(x,R)
        frozen=[]; actual=[]
        for i,y in enumerate(children(x)):
            ss,uu,kk=y
            logw=p*(ss-s)+q*(uu-u)-q/2
            ri=h(s,i,R)/D; rchild=rank(y,R)
            frozen.append(math.exp(logw-q*(ri-r)))
            actual.append(math.exp(logw-q*(rchild-r)))
            assert abs(rchild-ri)<=4/D+1e-11
            if i<s and i>=k:
                delta=i*(R-1)/(D*(D+R-1))
                assert abs(ri-rchild-delta)<1e-11
                assert delta<=1/D
            else:
                assert rchild>=ri-1e-11
        # Integrate each open piece using its left limiting formula.
        bounds=sorted({0,s,k,m})
        integral=0.0
        for lo,hi in zip(bounds,bounds[1:]):
            if hi==lo: continue
            if lo<s: logw=-p+(q if lo>=k else 0)-q/2; slope=q/D
            else: logw=p-(q if lo<k else 0)-q/2; slope=q*R/D
            left=math.exp(logw-q*(h(s,lo,R)/D-r))
            integral += left*(-math.expm1(-slope*(hi-lo)))/slope
        lam=D*bnorm/R
        S=sum(frozen); A=sum(actual)
        tol=3e-9*(1+S+A+lam)
        assert abs(integral-lam)<=tol
        assert S>=lam-tol
        assert S-lam<=3*math.sqrt(2)+tol
        deriv_R=(-k*u if k<=s else -s*(m-k))/(D*D)
        B=r+q*math.exp(-q)*deriv_R
        assert abs(B)<=1+1e-12
        dt=lam-bnorm*B
        U=(q+3*math.sqrt(2)*(q+1))*math.exp(q/D)+1
        low=4*q+1
        assert A<=math.exp(q/D)*S+tol
        assert A>=math.exp(-4*q/D)*lam-tol
        assert (A-dt)/bnorm<=U+tol/bnorm
        assert (dt-A)/bnorm<=low+tol/bnorm
        worst_upper=max(worst_upper,(A-dt)/(bnorm*U))
        worst_lower=max(worst_lower,(dt-A)/(bnorm*low))
        residual_checks+=1

# Exact counts by a separate direct word enumeration, including the refinement.
words=[((0,),0,{0:1})]
counts={0:1,1:1}; refinement=None
for length in range(2,11):
    nxt=[]
    for w,asc,used in words:
        for z in range(asc+2):
            if used.get(z,0)==2: continue
            u=dict(used); u[z]=u.get(z,0)+1
            nxt.append((w+(z,),asc+(z>w[-1]),u))
    words=nxt; counts[length]=len(words)
    if length==7:
        refinement=Counter(sum(v==2 for v in u.values()) for _,_,u in words)
exact={int(n):int(a) for n,a in (line.split() for line in (RESEARCH/'numerics/exact-counts-400.txt').read_text().splitlines())}
assert all(exact[n]==a for n,a in counts.items())
assert refinement==Counter({0:1,1:21,2:126,3:129})
z=sp.symbols('z')
discriminant=int(sp.discriminant(1+21*z+126*z*z+129*z**3,z))
assert discriminant==-84159
assert 2*exact[1]**2==exact[0]*exact[2]
assert all((j+1)*exact[j]**2>j*exact[j-1]*exact[j+1] for j in range(2,400))
b=[Fraction(exact[n],math.factorial(n)) for n in range(4)]
pf3=b[1]*(b[1]**2-b[2]*b[0])-b[2]*b[0]*b[1]+b[3]*b[0]**2
assert pf3==Fraction(-1,3)

# Separate exact suffix-count check for arbitrary small initial states.
@cache
def suffix(x,j):
    return 1 if j==0 else sum(suffix(y,j-1) for y in children(x))
allstate_lc=0
for x in states:
    if x[0]+x[1]>8: continue
    vals=[suffix(x,j) for j in range(17)]
    for j in range(1,16):
        assert (j+1)*vals[j]**2>=j*vals[j-1]*vals[j+1]
        allstate_lc+=1
assert allstate_lc==3060

# Exact symbolic simplification of the continuum averaged residual.
q,R,z,I=sp.symbols('q R z I')
avg_a=1-z+(R-1)/2+(2-R)*z*z/2-R*I
em=q*z/(2*R)+q*(1-z)/2
avg_B=sp.Rational(1,2)-q*(2-R)*z*(1-z)/(2*R)
assert sp.simplify(em-q*avg_a/R+avg_B-(q*I+q*(z-1)/(2*R)+sp.Rational(1,2)))==0

# Analytic Chernoff ingredients sampled independently (diagnostics only).
mp.mp.dps=55
T=3*mp.pi**2/8

def p(v): return mp.log(2*mp.exp(v)-1)/2
def bfun(v): return mp.sqrt(2*mp.exp(v)-1)*(-mp.expm1(-v))/v if v else mp.mpf(1)
def t(v): return T-mp.quad(lambda w:1/bfun(w),[v,v+20,mp.inf])
def d(v): return 1/(t(v)*bfun(v))
def dprime(v):
    dv=d(v); return dv*(-dv-1/(2-mp.exp(-v))-1/mp.expm1(v)+1/v)
def p2(v): return -mp.exp(-v)/(2-mp.exp(-v))**2
chernoff_checks=0
for Q in [12,20,50,100]:
    M=1/((2-mp.exp(-Q))*d(Q))
    for v in [mp.mpf(j)/10 for j in range(-10,11)]:
        h2=p2(Q+v)-M*dprime(Q+v)
        assert abs(h2)<=1
        if abs(v)<=mp.mpf('.5'): assert M*d(Q+v)>=mp.mpf('.25')
        chernoff_checks+=1

result={
 'purpose':'Independent finite diagnostics; analytic proof is audited separately.',
 'state_count':len(states),'max_m':20,'moment_identities_checked':4*len(states),
 'padding_transition_checks':padchecks,'weighted_residual_checks':residual_checks,
 'q_values':qs,'maximum_upper_residual_fraction':worst_upper,
 'maximum_lower_residual_fraction':worst_lower,
 'direct_word_counts':counts,'length_seven_double_letter_polynomial':[refinement[j] for j in range(4)],
 'polynomial_discriminant':discriminant,'PF3_minor':str(pf3),
 'exact_normalized_logconcavity_centers':'2–399 strict, 1 equality',
 'arbitrary_state_logconcavity_checks':allstate_lc,'continuum_average_symbolic_identity':True,'bounded_shift_calculus_checks':chernoff_checks,
 'all_checks_passed':True,
 'reviewed_numerical_data_sha256':hashlib.sha256((RESEARCH/'numerics/exact-counts-400.txt').read_bytes()).hexdigest()
}
(HERE/'independent-check-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
