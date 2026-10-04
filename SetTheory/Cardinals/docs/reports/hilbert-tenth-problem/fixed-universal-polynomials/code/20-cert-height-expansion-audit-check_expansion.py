#!/usr/bin/env python3
"""Independent bounded checks: exact rational algebra plus high-precision analysis.
No upstream executable import, no saved graph, no integer Pell tuple.
Numerical checks are corroborative, not interval-certified proofs.
"""
import hashlib,json,math
from fractions import Fraction as F
from pathlib import Path
import mpmath as mp

COUNTS={}
def need(ok,label):
    if not ok: raise RuntimeError(label)
    COUNTS[label]=COUNTS.get(label,0)+1

BRANCHES={
 'A+': {'p':(F(2,3),F(2,3)),'y':(F(1,3),F(-2,3)), 'N':(F(4,3),F(4,3),F(-7,3),F(-1,3)), 'h':(F(-1,3),F(25,36),F(-11,81))},
 'A-': {'p':(F(2,3),F(-2,3)),'y':(F(1,3),F(-4,3)), 'N':(F(4,3),F(-4),F(3),F(-1,3)), 'h':(F(1),F(1,4),F(0))},
 'B': {'p':(F(5,7),F(5,7)),'y':(F(15,28),F(-13,28)), 'N':(F(25,14),F(25,14),F(-39,14),F(-11,14)), 'h':(F(-1,3),F(142,225),F(-104,2025))},
}
def val(z): return mp.mpf(z.numerator)/z.denominator

def analytic(name,r):
    b=BRANCHES[name]
    pp,pc=map(val,b['p']); yp,yc=map(val,b['y'])
    p=pp*r+pc; y=yp*r+yc; L=p+y+1
    X=mp.power(2,p);Y=mp.power(2,y)
    A=X*Y+Y+2; alpha=mp.acosh(A)
    # This route computes the real interpolation directly from hyperbolic functions.
    S=mp.sinh(p*alpha)**2; beta=mp.acosh(S)
    logH=mp.log(mp.sinh(r*beta))-mp.log(mp.sinh(beta))
    N=(r-1)*(2*p*L-1); B=2*p*(r-1)
    d=1/X+2/(X*Y); a=1/A**2; bsmall=1/S**2
    u=mp.exp(-2*p*alpha); v=mp.exp(-2*r*beta)
    def g(z):
        # Equivalent stable form of log((1+sqrt(1-z))/2).
        return mp.log1p(-z/(2*(1+mp.sqrt(1-z))))
    rhs=B*(mp.log1p(d)+g(a))+2*(r-1)*mp.log1p(-u)+r*g(bsmall)-mp.log1p(-bsmall)/2+mp.log1p(-v)
    return {'p':p,'y':y,'N':N,'B':B,'d':d,'a':a,'b':bsmall,'u':u,'v':v,'ell':logH/mp.log(2),'rhs':rhs}

def polynomial(name,r):
    g,b2,b1,b0=map(val,BRANCHES[name]['N'])
    return ((g*r+b2)*r+b1)*r+b0

def derivatives(name,r):
    g,b2,b1,_=map(val,BRANCHES[name]['N'])
    return 3*g*r*r+2*b2*r+b1,6*g*r+2*b2

def T(name,r):
    pp,pc=map(val,BRANCHES[name]['p'])
    p=pp*r+pc; B=2*p*(r-1)
    return B*mp.power(2,-p)/(mp.log(2)*derivatives(name,r)[0])

# Exact rational checks: branch derivatives, coefficient budget, and series algebra.
for name,b in BRANCHES.items():
    p1,p0=b['p']; y1,y0=b['y']; gamma,b2,b1,b0=b['N']
    for r in [F(100)+F(k,4) for k in range(401)]+[F(1000),F(10**6)]:
        p=p1*r+p0; y=y1*r+y0; B=2*p*(r-1)
        Bprime=2*(p1*(r-1)+p)
        Nprime=3*gamma*r*r+2*b2*r+b1; Nsecond=6*gamma*r+2*b2
        need(Nprime>3*r*r and 0<Nsecond<12*r, 'rational cubic derivative envelopes')
        need(B<2*r*r and 0<Bprime/B<=3/r, 'rational B derivative envelopes')
        need(p>=16 and y>=3 and r<2*p, 'real interpolation domain')
        need(B/(F(2,3)*Nprime)<1, 'rational coefficient margin using ln2 greater than 2/3')
        need(Bprime/B+Nsecond/Nprime+p1<2, 'rational logarithmic T derivative margin')
        N=((gamma*r+b2)*r+b1)*r+b0
        need(N==(r-1)*(2*p*(p+y+1)-1), 'real cubic resonance identity')
    need(F(1,2)+F(1,16)+F(1,8*16)+F(1,16*16)+F(1,8)<1,'E5 explicit budget')

# Power-series coefficient recursion in h(w), using only Fraction arithmetic.
def mul(a,b,n):
    out=[F(0)]*(n+1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            if i+j<=n: out[i+j]+=x*y
    return out

def coefficient_equation(h,params,n):
    gamma,b2,b1,b0=params
    h2=mul(h,h,n); h3=mul(h2,h,n)
    out=h3[:]
    for k in range(n+1):
        if k>=1: out[k]+=(b2/gamma)*h2[k-1]
        if k>=2: out[k]+=(b1/gamma)*h[k-2]
        if k==3: out[k]+=b0/gamma
    out[0]-=1
    return out
series={}
for name,b in BRANCHES.items():
    h=[F(1)]+[F(0)]*12
    for k in range(1,13):
        h[k]=-coefficient_equation(h,b['N'],12)[k]/3
    need(tuple(h[1:4])==b['h'],'displayed Puiseux coefficients exact')
    need(all(z==0 for z in coefficient_equation(h,b['N'],12)), '12-order algebraic inverse residual')
    series[name]=[str(z) for z in h]

for j in range(1,1001):
    cj=F(math.comb(2*j,j),2*j*4**j)
    need(0<cj<=F(1,2*j),'central binomial coefficient envelope')

# Direct numerical checks at high precision; absolute error scales set by d^(k+1).
rows=[]
for name in BRANCHES:
    for rfrac in [F(100),F(201,2),F(101),F(143),F(250),F(512)]:
        pest=BRANCHES[name]['p'][0]*rfrac+BRANCHES[name]['p'][1]
        dps=math.ceil(8*float(pest)*math.log10(2))+100
        with mp.workdps(dps):
            r=val(rfrac); z=analytic(name,r)
            B,d,a,b,u,v=[z[k] for k in ['B','d','a','b','u','v']]
            left=(z['ell']-z['N'])*mp.log(2)
            scale=B*d**5
            need(abs(left-z['rhs'])<scale*mp.mpf('1e-20'),'direct hyperbolic E1 identity')
            need(all(0<t<=d*d/16 for t in [a,b,u,v]),'E4 scale envelopes')
            need(abs(z['ell']-z['N']-B*d/mp.log(2))<B*d*d/mp.log(2),'E5 uniform leading bound')
            maxratio=mp.mpf(0)
            partial=mp.mpf(0)
            for k in range(1,5):
                cj=mp.mpf(math.comb(2*k,k))/(2*k*4**k)
                partial+=B*(-1)**(k+1)*d**k/k-B*cj*a**k-2*(r-1)*u**k/k+(mp.mpf(1)/(2*k)-r*cj)*b**k-v**k/k
                tail=B*d**(k+1)/(k+1)+B*a**(k+1)/(2*(k+1)*(1-a))+2*(r-1)*u**(k+1)/((k+1)*(1-u))+(r+1)*b**(k+1)/(2*(k+1)*(1-b))+v**(k+1)/((k+1)*(1-v))
                ratio=abs(z['rhs']-partial)/tail
                need(ratio<=1+mp.mpf('1e-50'),'E3 truncated series tail')
                maxratio=max(maxratio,ratio)
            # Independently solve the cubic for the direct hyperbolic log height.
            r0=r+(z['ell']-z['N'])/derivatives(name,r)[0]
            for _ in range(8):
                r0-=(polynomial(name,r0)-z['ell'])/derivatives(name,r0)[0]
            need(abs(polynomial(name,r0)-z['ell'])<mp.power(10,-dps+30),'cubic inverse residual')
            delta=r0-r
            need(0<delta<2*d<1,'inverse displacement envelope')
            p1,pconstant=map(val,BRANCHES[name]['p']); y1,yconstant=map(val,BRANCHES[name]['y'])
            p0=p1*r0+pconstant; y0=y1*r0+yconstant
            error=abs(r-r0+T(name,r0))
            bound=64*(mp.power(2,-p0-y0)+mp.power(2,-2*p0))
            need(error<bound,'E7 explicit 64 inverse bound')
            q=mp.power(2,-z['p']); Bprime=2*(p1*(r-1)+z['p'])
            Np,Npp=derivatives(name,r)
            Tprime=T(name,r)*(Bprime/B-Npp/Np-p1*mp.log(2))
            need(abs(Tprime)<2*q,'T derivative bound')
            ahead=analytic(name,r+mp.mpf('0.01'))
            need(ahead['ell']>z['ell'],'real interpolation monotonicity')
            rows.append({'branch':name,'R':str(rfrac),'decimal_precision':dps,'E3_max_ratio':mp.nstr(maxratio,20),'E7_error_to_bound':mp.nstr(error/bound,20),'delta':mp.nstr(delta,12)})

# Independent generic g-series tests, where every listed scale is numerically visible.
with mp.workdps(120):
    for z in [mp.mpf('0.01'),mp.mpf('0.25'),mp.mpf('0.5'),mp.mpf('0.9')]:
        g=mp.log((1+mp.sqrt(1-z))/2)
        partial=mp.mpf(0)
        for k in range(1,61):
            partial-=mp.mpf(math.comb(2*k,k))*z**k/(2*k*4**k)
            tail=z**(k+1)/(2*(k+1)*(1-z))
            need(abs(g-partial)<=tail+mp.mpf('1e-115'),'g generic series and tail')

out={'status':'PASS','upstream_code_executed':False,'saved_schedule_executed':False,'integer_witness_tuple_materialized':False,
 'numerical_checks_are_interval_certified':False,'mpmath_version':mp.__version__,
 'counts':dict(sorted(COUNTS.items())),'analytic_cases':rows,'algebraic_inverse_h_coefficients_through_order_12':series}
print(json.dumps(out,indent=2,sort_keys=True))
