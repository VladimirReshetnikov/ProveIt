#!/usr/bin/env python3
"""Reproduce exact checks and numerical illustrations for the accompanying article.

Requires Python >=3.10, SymPy and mpmath. Run: python verify.py
The symbolic identities are finite exact checks, not a formal proof-assistant audit.
Numerical asymptotic comparisons illustrate, but do not prove, the analytic theorems.
"""
from __future__ import annotations
import csv
import json
import math
import sys
import time
from functools import lru_cache
from pathlib import Path
import sympy as sp
import mpmath as mp
from certificate_data import A_ROWS, B_ROWS

ROOT = Path(__file__).resolve().parent
n, t, z = sp.symbols('n t z')

def p_polynomials():
    return [
        -2*(n+1)*(n+2)*(65*n**3+593*n**2+1772*n+1740),
        2015*n**5+24428*n**4+114387*n**3+258294*n**2+281088*n+118368,
        -4*(910*n**5+11032*n**4+52047*n**3+119686*n**2+134365*n+58980),
        3*(3*n+8)*(3*n+10)*(65*n**3+398*n**2+781*n+496)]

def q_polynomials():
    R=65*n**3+593*n**2+1772*n+1740
    S=65*n**3+398*n**2+781*n+496
    p=p_polynomials()
    return [-18*(n+1)*(3*n+2)*(3*n+4)*(3*n+5)*(3*n+7)*R,
            3*(n+2)*(3*n+5)*(3*n+7)*p[1],
            (n+2)*(n+3)**2*p[2],
            (n+2)*(n+3)**2*(n+4)**2*S]

def horner(row, variable):
    result=sp.Integer(0)
    for c in row: result=result*variable+c
    return result

def verify_certificate():
    D=t*t-1
    A=-2*t*sum(horner(row,n+2)*t**j for j,row in enumerate(A_ROWS))/((n+2)*D**2)
    B=2*t*t*sum(horner(row,n+2)*t**j for j,row in enumerate(B_ROWS))/((n+2)*D**2)
    P=[sp.Matrix([1,0]),sp.Matrix([0,1])]
    for j in (1,2):
        P.append(((2*(n+j)+1)*t*P[j]-(n+j)*P[j-1])/(n+j+1))
    q=q_polynomials()
    rhs=sum((q[j]*(4*t**3/D)**j*P[j] for j in range(4)),sp.zeros(2,1))
    L=(3*n+1)/t-(n+1)/(t-1)-(n+2)/(t+1)
    residuals=[sp.diff(A,t)+L*A-(n+1)*t*A/D-(n+1)*B/D-rhs[0],
               sp.diff(B,t)+L*B+(n+1)*A/D+(n+1)*t*B/D-rhs[1]]
    assert all(sp.cancel(r)==0 for r in residuals)
    lam=9*(3*n+2)*(3*n+4)*(3*n+5)*(3*n+7)/(n+2)
    for j in range(4):
        ratio=sp.Integer(1)*sp.prod((n+k)*(n+k+1)**2 for k in range(1,j+1))/sp.prod(3*n+k for k in range(2,3*j+2))
        assert sp.cancel(q[j]-lam*p_polynomials()[j]*ratio)==0
    assert sp.expand(sum(p*(3*(n+j)+2) for j,p in enumerate(p_polynomials())))==0
    print('PASS: both rational telescoping identities, all four normalization identities, and the exact linear solution.')

def verify_resolvent():
    r=sp.symbols('r0:4'); v=sp.symbols('v')
    from itertools import combinations
    e=[None]+[sum(sp.prod(c) for c in combinations(r,k)) for k in range(1,5)]
    e1,e2,e3,e4=e[1:]
    proposed=(v**6-e2*v**5+(e1*e3-e4)*v**4
              -(e3**2+e1**2*e4-2*e2*e4)*v**3
              +e4*(e1*e3-e4)*v**2-e2*e4**2*v+e4**3)
    assert sp.expand(sp.prod(v-r[i]*r[j] for i,j in combinations(range(4),2))-proposed)==0
    a,b,c,d,e0,Y=sp.symbols('a b c d e Y')
    A=a*e0;B=b*d;C=a*d*d+b*b*e0;T=1-c;U=A*Y*Y
    sextic=A**3*Y**6-A**2*T*Y**5+A*(B-A)*Y**4+(2*A*T+C)*Y**3+(B-A)*Y**2-T*Y+1
    compact=(1-U)**2*(1+U-T*Y)+(1+U)*B*Y**2+C*Y**3
    assert sp.expand(sextic-compact)==0
    # Rebuild the generic resolvent independently in elementary-symmetric symbols.
    E1,E2,E3,E4=sp.symbols('E1:5')
    res=v**6-E2*v**5+(E1*E3-E4)*v**4-(E3**2+E1**2*E4-2*E2*E4)*v**3+E4*(E1*E3-E4)*v**2-E2*E4**2*v+E4**3
    res=res.subs({E1:-d/e0,E2:(c-1)/e0,E3:-b/e0,E4:a/e0,v:-a*Y})
    assert sp.cancel(res*e0**3/a**3-sextic)==0
    print('PASS: generic quartic pair-product resolvent and marked excursion sextic.')

def C_exact(k: int) -> int:
    if k<0: raise ValueError('k must be nonnegative')
    if k==0: return 1
    # [u^j](1+u)^(3k+1)/(1-u)^(2k).
    coeff=[sum(math.comb(3*k+1,h)*math.comb(2*k+j-h-1,j-h)
               for h in range(j+1)) for j in range(k+1)]
    return sum(math.comb(k,h)**2*coeff[k-h] for h in range(k+1))

def a_from_C(k: int, C: int) -> int:
    num=math.factorial(5*k)*C
    den=math.factorial(k)**2*math.factorial(3*k+1)
    a,rem=divmod(num,den)
    assert rem==0
    return a

def C_recurrence(maximum: int) -> list[int]:
    if maximum<0: raise ValueError('maximum must be nonnegative')
    values=[1,7,104]
    qf=[sp.lambdify(n,p,'math') for p in q_polynomials()]
    for k in range(maximum-2):
        num=-sum(int(qf[j](k))*values[k+j] for j in range(3))
        nxt,rem=divmod(num,int(qf[3](k)))
        assert rem==0 and nxt>0
        values.append(nxt)
    return values[:maximum+1]

def fixed_content_counts(r: int, maximum: int) -> list[int]:
    if r<2 or maximum<0: raise ValueError('r >= 2 and maximum >= 0 required')
    steps=tuple(2*i-r-1 for i in range(1,r+1))
    @lru_cache(None)
    def f(k: tuple[int,...]) -> int:
        if not any(k): return 1
        if sum(s*v for s,v in zip(steps,k))<0: return 0
        total=0
        for i,c in enumerate(k):
            if c:
                prev=list(k);prev[i]-=1
                total+=f(tuple(prev))
        return total
    return [f((k,)*r) for k in range(maximum+1)]

def asymptotic_coefficients(order: int=8):
    if order<1: raise ValueError('order must be at least one')
    rho=(3-sp.sqrt(5))/2
    coeff=[rho,1-4*sp.sqrt(5)/25]
    P=[sp.Poly(sp.expand(p.subs(n,1/z)*z**5),z) for p in p_polynomials()]
    # Coefficient of z^(k+2) in the normalized recurrence. This is triangular.
    for k in range(2,order+1):
        ck=sp.Symbol('ck');current=coeff+[ck];res=sp.Integer(0)
        for j,p in enumerate(P):
            for (a,),v in p.terms():
                for ell,c in enumerate(current):
                    h=k+2-a-ell
                    if h>=0:
                        res+=v*c*sp.binomial(1-ell,h)*j**h
        assert sp.simplify(sp.diff(res,ck)-1625*k*(k-1))==0
        ckvalue=sp.simplify(-res.subs(ck,0)/sp.diff(res,ck))
        assert sp.simplify(res.subs(ck,ckvalue))==0
        coeff.append(ckvalue)
    logstirling=sum(sp.bernoulli(2*k)/(2*k*(2*k-1))*(sp.Rational(1,5**(2*k-1))-5)*z**(2*k-1)
                    for k in range(1,(order+1)//2+1) if 2*k-1<=order)
    # Truncated exponential computed without a costly general symbolic series.
    e=[sp.Integer(1)]
    logs=sp.Poly(logstirling,z)
    for k in range(1,order+1):
        e.append(sp.expand(sum(j*logs.nth(j)*e[k-j] for j in range(1,k+1))/k))
    factor=[sum(e[j]*(-1)**(k-j)*(k-j+1) for j in range(k+1)) for k in range(order+1)]
    d=[sp.simplify(sum(coeff[j]*factor[k-j] for j in range(k+1))/rho) for k in range(order+1)]
    return coeff,d

def saddle_check():
    # Independent Gaussian-moment calculation of the first saddle correction.
    rho=(3-sp.sqrt(5))/2;u=sp.expand(rho**2)
    x,y,q=sp.symbols('x y q');b=sp.log(1+q);g=-sp.log(1-q);K={}
    for j in range(1,5):
        b=sp.factor(q*sp.diff(b,q));g=sp.factor(q*sp.diff(g,q))
        if j>=2:
            K[j]=sp.expand(sp.simplify(3*b.subs(q,u)+2*g.subs(q,u))*x**j+sp.simplify(b.subs(q,rho))*(y**j+(x-y)**j))
    H=sp.Matrix([[sp.expand(K[2]).coeff(x,2),sp.expand(K[2]).coeff(x,1).coeff(y,1)/2],
                 [sp.expand(K[2]).coeff(x,1).coeff(y,1)/2,sp.expand(K[2]).coeff(y,2)]]).applyfunc(sp.simplify)
    assert H==sp.Matrix([[sp.Rational(14,15),sp.Rational(-1,5)],[sp.Rational(-1,5),sp.Rational(2,5)]])
    V=H.inv()
    @lru_cache(None)
    def moment(a,b):
        if a<0 or b<0 or (a+b)%2: return sp.Integer(0)
        if a+b==0:return sp.Integer(1)
        if a:return (a-1)*V[0,0]*moment(a-2,b)+b*V[0,1]*moment(a-1,b-1)
        return (b-1)*V[1,1]*moment(0,b-2)
    amp=1+u
    correction=-u*x*x/2+u*x*K[3]/6+amp*K[4]/24-amp*K[3]**2/72
    dC=sp.simplify(sum(v*moment(a,b) for (a,b),v in sp.Poly(correction,x,y).terms())/amp)
    assert sp.simplify(dC+sp.Rational(71,90)-13*sp.sqrt(5)/50)==0
    print('PASS: saddle Hessian and exact first Gaussian correction.')

def constants():
    w=sp.symbols('w');result=[]
    for r in range(2,9):
        steps=[i-(r+1)//2 for i in range(1,r+1)] if r%2 else [2*i-r-1 for i in range(1,r+1)]
        b=-min(steps)
        Q=r*w**b-sum(w**(b+s) for s in steps)
        reduced=sp.div(Q,(w-1)**2,w)[0]
        assert sp.rem(Q,(w-1)**2,w)==0
        roots=sp.nroots(reduced,n=55,maxsteps=300) if sp.degree(reduced,w)>0 else []
        inside=[mp.mpc(str(sp.re(x)),str(sp.im(x))) for x in roots if abs(complex(x))<1-1e-8]
        assert len(inside)==b-1
        E=mp.re((-1)**(b+1)*r*mp.fprod(inside))
        c=E/(mp.sqrt(r)*mp.power(2,mp.mpf(r-1)/2))
        result.append({'r':r,'E':mp.nstr(E,35),'c':mp.nstr(c,35)})
    return result

def main():
    start=time.perf_counter();mp.mp.dps=100
    if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
    verify_resolvent();verify_certificate();saddle_check()
    C=C_recurrence(1000)
    assert all(C[k]==C_exact(k) for k in range(104))
    print('PASS: recurrence agrees with independent positive coefficient formula for n=0..103.')
    known=[1,35,18720,19369350,27032968200,44776592395920,82881380383401600,
           165850226337286576800,351597937025844947295000,
           779279938350147159519336600,1789294251011628021153241548800,
           4228135363283244543270651711564000,10232120200642411474243152429724152000]
    assert [a_from_C(k,C[k]) for k in range(len(known))]==known
    rows={r:fixed_content_counts(r,limit) for r,limit in [(2,10),(3,10),(4,10),(5,8),(6,5),(7,4)]}
    assert rows[5]==known[:9]
    assert rows[4][:7]==[1,7,403,40350,5223915,783353872,129141898872]
    print('PASS: independent content-state DP, including A215570 n=0..8 and OEIS initial values.')
    c,d=asymptotic_coefficients(8)
    assert sp.simplify(d[1]+sp.Rational(13,10)-13*sp.sqrt(5)/50)==0
    with open(ROOT/'a215570_terms.csv','w',newline='') as f:
        writer=csv.writer(f);writer.writerow(['n','C_n','A215570_n'])
        writer.writerows((k,C[k],a_from_C(k,C[k])) for k in range(104))
    errors=[];lead=(3*mp.sqrt(5)-5)/(8*mp.pi**2)
    ds=[mp.mpf(str(sp.N(x,105))) for x in d]
    for k in [20,50,100,250,1000]:
        exact=mp.mpf(a_from_C(k,C[k]));base=lead*mp.power(5,5*k)/k**3
        er={'n':k}
        for order in [0,1,2,4,8]:
            estimate=base*sum(ds[j]/mp.mpf(k)**j for j in range(order+1))
            er['relative_error_order_'+str(order)]=mp.nstr(estimate/exact-1,16)
        errors.append(er)
    out={'asymptotic_d':[str(x) for x in d], 'normalized_c':[str(x) for x in c],
         'constants':constants(),'numerical_relative_errors':errors,
         'exact_DP_rows':{str(k):v for k,v in rows.items()},
         'symbolic_certificate':'Both identities verified identically over Q(n,t)',
         'C_formula_range':'0..103', 'C_recurrence_generated_range':'0..1000',
         'runtime_seconds':round(time.perf_counter()-start,3),
         'python':sys.version.split()[0], 'sympy':sp.__version__, 'mpmath':mp.__version__}
    (ROOT/'verification_results.json').write_text(json.dumps(out,indent=2)+'\n')
    print('First asymptotic correction coefficients:',*[str(x) for x in d[:5]],sep='\n  ')
    print('Numerical relative errors:',json.dumps(errors,indent=2))
    print('PASS: all checks completed; data written beside this script.')
    print('Elapsed seconds:',out['runtime_seconds'])

if __name__=='__main__': main()
