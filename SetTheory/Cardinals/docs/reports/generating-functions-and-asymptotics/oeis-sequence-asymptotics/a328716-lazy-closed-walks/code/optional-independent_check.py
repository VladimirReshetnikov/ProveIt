#!/usr/bin/env python3
"""Independent ODE/raw-moment, Gaussian-series and exact occupancy checks."""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
from math import comb, factorial
from fractions import Fraction
import json
import sympy as sy
import mpmath as mp

HERE=Path(__file__).absolute().parent
SOURCE=HERE.parent/'data'
from utility import finish, need
mp.mp.dps=90
b,j,t=sy.symbols('b j t')
R=3
x=(b+1)/4
# g_m = r^m F^(m)(r)/F(r). Differentiate z^2 F''+z F'-4z^2 F=0.
g=[sy.Integer(1),sy.Integer(1)]
for m in range(2*R+1):
    nxt=-(2*m+1)*g[m+1]-(m*m-4*x)*g[m]
    if m>=1: nxt+=8*m*x*g[m-1]
    if m>=2: nxt+=4*m*(m-1)*x*g[m-2]
    g.append(sy.expand(nxt))
mom=[sy.Integer(1)]
kap=[sy.Integer(0)]
for k in range(1,2*R+3):
    mom.append(sy.expand(sum(sy.functions.combinatorial.numbers.stirling(k,h,kind=2)*g[h] for h in range(1,k+1))))
    kap.append(sy.factor(mom[k]-sum(comb(k-1,h-1)*kap[h]*mom[k-h] for h in range(1,k))))

# Expand exp(sum_{k>=1} e_k h^k) by its differential recurrence.
# The amplitude z^j contributes exp(i*j*t*h), so it simply adds to e_1.
e=[0]+[kap[k+2]*(sy.I*t)**(k+2)/sy.factorial(k+2) for k in range(1,2*R+1)]
e[1]+=sy.I*j*t
P=[sy.Integer(1)]
for k in range(1,2*R+1):
    P.append(sy.expand(sum(h*e[h]*P[k-h] for h in range(1,k+1))/k))
def normal_mean(poly):
    ans=0
    for (degree,),coefficient in sy.Poly(poly,t).terms():
        if degree%2==0:
            ans+=coefficient*sy.factorial2(degree-1)/b**(degree//2)
    return sy.factor(ans)
need(all(normal_mean(P[k])==0 for k in range(1,2*R+1,2)), "optional independent identity failed")
S=[normal_mean(P[2*k]) for k in range(R+1)]
st=[sy.Integer(1),sy.Rational(1,12),sy.Rational(1,288),-sy.Rational(139,51840)]
C=[sy.factor(sum(st[k]*S[m-k] for k in range(m+1))) for m in range(R+1)]
v=sy.symbols('v')
def parity_mean(poly):
    ans=0
    for (degree,),coefficient in sy.Poly(poly,j).terms():
        moment=sum(sy.functions.combinatorial.numbers.stirling(degree,h,kind=2)*x**(h//2)*(v if h%2 else 1) for h in range(degree+1))
        ans+=coefficient*moment
    return sy.factor(ans)
Ce=[parity_mean(poly) for poly in C]
source=json.loads((SOURCE/'walk_checks.json').read_text())
for k in range(R+1):
    need(sy.factor(Ce[k]-sy.sympify(source['c_symbolic'][k]))==0, "optional independent identity failed")
for k in range(1,2*R+3):
    need(sy.factor(kap[k]-sy.sympify(source['cumulants'][k-1]))==0, "optional independent identity failed")
Q=[sy.Integer(1)]
for k in range(1,R+1):
    Q.append(sy.factor(C[k]-sum(Ce[h]*Q[k-h] for h in range(1,k+1))))
    need(parity_mean(Q[k])==0, "optional independent identity failed")
need(sy.factor(Q[1]+(j*j-x-v)/(2*b)-(j-v)/b**2)==0, "optional independent identity failed")

r=mp.findroot(lambda z:2*z*mp.besseli(1,2*z)/mp.besseli(0,2*z)-1,mp.mpf('.8'))
bv=4*r*r-1
f=mp.besseli(0,2*r)
q=1/f;p=1-q;tau=p*q-q*q/bv
d=f/(mp.e*r)
def em(u,eps):return mp.exp(r*u)+eps*mp.exp(-r*u)
def num(expr, vv):return mp.mpf(str(expr.subs({b:sy.Float(str(bv),95),v:sy.Float(str(vv),95)}).evalf(85)))
for k in range(1,9):
    derivative=mp.diff(lambda s:mp.log(mp.besseli(0,2*r*mp.exp(s))),0,k)
    need(abs(derivative-num(kap[k],0))<mp.mpf('1e-75'), "optional independent identity failed")

# Integer bivariate counts via nonempty coordinate blocks, independent of
# the supplied dimension-by-dimension binomial convolution.
N=121; max_pairs=N//2
positive=[[0]*(max_pairs+1) for _ in range(max_pairs+1)]
positive[0][0]=1
for axes in range(1,max_pairs+1):
    for pairs in range(axes,max_pairs+1):
        positive[axes][pairs]=sum(comb(pairs,h)**2*positive[axes-1][pairs-h] for h in range(1,pairs+1))
def exact_joint(n):
    data=[]
    for pairs in range(n//2+1):
        zeros=n-2*pairs
        multiplier=comb(n,zeros)*comb(2*pairs,pairs)
        for axes in range(min(n,pairs)+1):
            count=multiplier*comb(n,axes)*positive[axes][pairs]
            if count:data.append((zeros,axes,count))
    return data
def count_riccati(n):
    m=n//2; a=[Fraction(0)]; c=[Fraction(1)]
    for k in range(1,m+1):
        a.append((Fraction(4 if k==1 else 0)-sum(a[h]*a[k-h] for h in range(1,k)))/(2*k))
        c.append(Fraction(n,2*k)*sum(a[h]*c[k-h] for h in range(1,k+1)))
    ans=factorial(n)*sum(c[k]/factorial(n-2*k) for k in range(m+1))
    need(ans.denominator==1, "optional independent identity failed")
    return ans.numerator
checks=[]
for n in [20,21,60,61,120,121]:
    eps=(-1)**n
    data=exact_joint(n); total=sum(count for _,_,count in data)
    need(total==count_riccati(n), "optional independent identity failed")
    zero_counts={}
    for zeros,axes,count in data:zero_counts[zeros]=zero_counts.get(zeros,0)+count
    vv=r*(mp.exp(r)-eps*mp.exp(-r))/em(1,eps)
    offset=-q/bv*(vv+(bv-1)/2-1/bv)
    mean=mp.mpf(sum(axes*count for _,axes,count in data))/total
    variance=mp.mpf(sum(axes**2*count for _,axes,count in data))/total-mean**2
    u0=mp.j*mp.pi/(2*r) if eps==1 else mp.j*mp.pi/r
    z0=r*u0
    DE=z0*(mp.exp(z0)-eps*mp.exp(-z0))
    expected=(-1/(2*bv)+1/bv**2)*DE
    marked=sum(mp.mpf(count)*u0**zeros for zeros,count in zero_counts.items())
    cancellation_scaled=n*marked/((d*n)**n/mp.sqrt(bv))
    cf_checks=[]
    for a,s in [(1,mp.mpf('.7')),(2,mp.mpf('1.2'))]:
        u=mp.exp(mp.j*s)
        actual=sum(mp.mpf(count)/total*mp.exp(mp.j*a*(axes-n*p)/mp.sqrt(n))*u**zeros for zeros,axes,count in data)
        target=mp.exp(-tau*a*a/2)*em(u,eps)/em(1,eps)
        cf_checks.append({'t':a,'s':str(s),'absolute_error':mp.nstr(abs(actual-target),24),'sqrt_n_error':mp.nstr(mp.sqrt(n)*abs(actual-target),24)})
    checks.append({'n':n,'exact_joint_equals_riccati':True,'occupation_mean_offset_residual_times_n':mp.nstr(n*(mean-n*p-offset),25),'variance_density':mp.nstr(variance/n,25),'amplitude_zero_scaled':str(cancellation_scaled),'amplitude_zero_limit':str(expected),'joint_characteristic_function':cf_checks})

out={'method':'Differentiated Bessel ODE raw moments; formal exponential differential recurrence; exact nonempty-coordinate decomposition','symbolic_c0_through_c3_match':True,'cumulants1_through8_match':True,'direct_bessel_log_derivatives1_through8_match':True,'probability_Q1_through_Q3':[str(expr) for expr in Q[1:]],'all_Q_centered':True,'checks':checks}
finish(out, HERE.parent/'data/independent_checks.json')
