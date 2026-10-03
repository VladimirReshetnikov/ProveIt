#!/usr/bin/env python3
"""Reproducible finite checks for fixed-composition excursions.

Exact counts and identities are checked with integers/Fractions. Root constants
and asymptotic diagnostics are numerical, NOT interval certificates or proofs.
Run from any directory: python code/verify.py
"""
from __future__ import annotations
from fractions import Fraction
from itertools import product
from math import factorial, gcd
from pathlib import Path
import json
import mpmath as mp
import sympy as sp

OUT = Path(__file__).resolve().parents[1] / 'data'
OUT.mkdir(exist_ok=True)
mp.mp.dps = 60

def steps(r: int) -> tuple[int, ...]:
    if r < 2:
        raise ValueError('r must be at least 2')
    g = gcd(2, r - 1)
    return tuple((2*i-r-1)//g for i in range(1,r+1))

def multinomial(k: tuple[int, ...]) -> int:
    ans=factorial(sum(k))
    for v in k:
        ans //= factorial(v)
    return ans

def dp_box(r: int, bound: int) -> tuple[list[int], list[int]]:
    """Counts all nonnegative paths in a rectangular count-vector box.

    Counts are stored in mixed-radix order, so each predecessor is already
    available. This is a finite enumeration, not an asymptotic algorithm.
    """
    if bound < 0 or (bound+1)**r > 3_000_000:
        raise ValueError('unsupported bound: use at most 3 million states')
    b=bound+1; s=steps(r)
    stride=[b**(r-1-i) for i in range(r)]
    values=[0]*(b**r); values[0]=1
    for idx,k in enumerate(product(range(b), repeat=r)):
        if idx==0 or sum(x*y for x,y in zip(k,s))<0:
            continue
        values[idx]=sum(values[idx-stride[i]] for i in range(r) if k[i])
    diagonal=[values[n*sum(stride)] for n in range(bound+1)]
    return diagonal,values

def kernel_constant(r: int) -> tuple[mp.mpf,str]:
    u=sp.Symbol('u'); ss=steps(r); h=-ss[0]
    q=sum(u**(v+h) for v in ss)-r*u**h
    reduced=sp.div(q,(u-1)**2,u)
    assert reduced[1]==0
    roots=sp.nroots(reduced[0],n=60,maxsteps=300) if sp.degree(reduced[0],u)>0 else []
    inside=[]
    for root in roots:
        z=mp.mpc(str(sp.re(root)),str(sp.im(root)))
        assert abs(abs(z)-1)>mp.mpf('1e-15')
        if abs(z)<1:
            inside.append(z)
    assert len(inside)==h-1
    value=(-1)**(h+1)*r*mp.fprod(inside)
    assert abs(mp.im(value))<mp.mpf('1e-50')
    return mp.re(value),str(sp.expand(reduced[0]))

def bridge_log_check(r: int,bound: int) -> int:
    _,allvalues=dp_box(r,bound)
    b=bound+1; stride=[b**(r-1-i) for i in range(r)];ss=steps(r)
    kk=[k for k in product(range(b),repeat=r) if sum(x*y for x,y in zip(k,ss))==0]
    kk.sort(key=lambda k:(sum(k),k))
    e={kk[0]:Fraction(1)}
    for k in kk[1:]:
        total=0
        for j in kk[1:]:
            if sum(j)>sum(k):break
            if all(x<=y for x,y in zip(j,k)):
                diff=tuple(y-x for x,y in zip(j,k))
                total+=multinomial(j)*e[diff]
        e[k]=Fraction(total,sum(k))
        assert e[k].denominator==1
        assert e[k]==allvalues[sum(x*y for x,y in zip(k,stride))]
    return len(kk)-1

def mul(a:list[int],b:list[int],n:int)->list[int]:
    ans=[0]*(n+1)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b[:n+1-i]):
                ans[i+j]+=x*y
    return ans

def powser(a:list[int],k:int,n:int)->list[int]:
    out=[1]+[0]*n
    for _ in range(k):out=mul(out,a,n)
    return out

def sextic_check(n:int=24)->None:
    # Independent height DP for weights 2,3,5,7,11 on -2,-1,0,1,2.
    ws=[2,3,5,7,11]; ss=[-2,-1,0,1,2];state={0:1};ee=[1]
    for _ in range(n):
        nxt={}
        for height,count in state.items():
            for step,weight in zip(ss,ws):
                if height+step>=0:
                    nxt[height+step]=nxt.get(height+step,0)+weight*count
        state=nxt;ee.append(state.get(0,0))
    a,b,c,d,e,X,t=sp.symbols('a b c d e X t')
    f=(a**3*e**3*X**6+a**2*e**2*(c-1)*X**5+
       (a*b*d*e-a**2*e**2)*X**4+
       (a*d**2+b**2*e+2*a*e*(1-c))*X**3+
       (b*d-a*e)*X**2+(c-1)*X+1)
    poly=sp.Poly(f.subs(dict(zip([a,b,c,d,e],[w*t for w in ws]))),X,t)
    acc=[0]*(n+1)
    powers=[powser(ee,k,n) for k in range(7)]
    for (k,j),coef in poly.terms():
        for z in range(n+1-j):acc[z+j]+=int(coef)*powers[k][z]
    assert not any(acc)

REFERENCE={
  4:[1,7,403,40350,5223915,783353872,129141898872,22745605840236,
     4206489449301315,807660192541534200,159752979289765273698],
  5:[1,35,18720,19369350,27032968200,44776592395920,82881380383401600,
     165850226337286576800,351597937025844947295000,779279938350147159519336600,
     1789294251011628021153241548800,4228135363283244543270651711564000,
     10232120200642411474243152429724152000],
  6:[1,139,746192,9212531290,164401445439455,3611684199828856072,
     90695437030756958966384],
  7:[1,1001,71892912,13126885205000,3627155158988429250],
}
# Two additional published b-file values; not independently generated here.
EXTERNAL5={20:20583327745215005844288257113206932906760798477397608945484080000,
50:942993553387261719839432368142529421305313544889687234217568261481733850928388393453200584613854491160136599571045529542095321859090899240127873178680468809691523430400}

def main()->None:
    log=[]; rows={}; constants={}
    for r,bound in [(2,24),(3,24),(4,18),(5,16),(6,6),(7,4)]:
        values,_=dp_box(r,bound); rows[r]=values
        if r==2:
            assert all(v==factorial(2*n)//(factorial(n)*factorial(n+1)) for n,v in enumerate(values))
        elif r==3:
            assert all(v==factorial(3*n)//(factorial(n)**3*(n+1)) for n,v in enumerate(values))
        else:
            assert values[:len(REFERENCE[r])]==REFERENCE[r]
        log.append(f'PASS exact DP r={r}, n=0..{bound}; {(bound+1)**r} rectangular states')
    for r in range(2,9):
        kap,pol=kernel_constant(r)
        cc=kap/(mp.sqrt(r)*mp.power(2,mp.mpf(r-1)/2))
        constants[r]={'kappa':mp.nstr(kap,48),'c_oeis':mp.nstr(cc,48),'reduced_kernel':pol}
        log.append(f'NUMERICAL r={r}: kappa={mp.nstr(kap,30)}, c={mp.nstr(cc,30)}')
    ph=(1+mp.sqrt(5))/2
    assert abs(mp.mpf(constants[4]['kappa'])-4*(ph-mp.sqrt(ph)))<mp.mpf('1e-45')
    assert abs(mp.mpf(constants[5]['kappa'])-5*(3-mp.sqrt(5))/2)<mp.mpf('1e-45')
    for r,b in [(2,4),(3,3),(4,3),(5,2),(6,2)]:
        count=bridge_log_check(r,b)
        log.append(f'PASS bridge logarithm identity r={r}, count bound {b}, {count} nonempty balanced vectors')
    sextic_check()
    log.append('PASS weighted basketball sextic through total length 24, weights (2,3,5,7,11)')
    a5=mp.mpf(13)*(mp.sqrt(5)-5)/50
    K5=(3*mp.sqrt(5)-5)/(8*mp.pi**2)
    diagnostics=[]
    for n in [4,8,12,16,20,50]:
        val=rows[5][n] if n<=16 else EXTERNAL5[n]
        lead=K5*mp.power(5,5*n)/n**3
        ratio=val/lead;lam=5*mp.log(5);beta=3
        # Keep the root exponent in arbitrary-precision arithmetic.
        x0=-beta/lam*mp.lambertw(-lam/beta*mp.power(K5/val,mp.mpf(1)/beta),-1)
        x1=x0-a5/(lam*x0)
        item={'n':n,'origin':'independent DP' if n<=16 else 'OEIS b-file',
              'ratio_to_leading':mp.nstr(ratio,25),
              'n_times_ratio_minus_one':mp.nstr(n*(ratio-1),25),
              'n2_after_first_correction':mp.nstr(n*n*(ratio-1-a5/n),25),
              'inverse_core_error':mp.nstr(x0-n,25),
              'inverse_corrected_error':mp.nstr(x1-n,25)}
        diagnostics.append(item)
        log.append('DIAGNOSTIC '+json.dumps(item))
    for r in [4,5,6,7]:
        n=len(rows[r])-1;kap=mp.mpf(constants[r]['kappa'])
        prob=mp.mpf(rows[r][n])*r*n/multinomial((n,)*r)
        log.append(f'DIAGNOSTIC r={r}, n={n}: rn*A/M={mp.nstr(prob,20)}, limiting kappa={mp.nstr(kap,20)}')
    (OUT/'exact_rows.json').write_text(json.dumps(rows,indent=2)+'\n')
    (OUT/'kernel_constants.json').write_text(json.dumps(constants,indent=2)+'\n')
    (OUT/'diagnostics.json').write_text(json.dumps(diagnostics,indent=2)+'\n')
    log.append('All finite exact assertions passed. Asymptotic convergence and D-finiteness are proved in the article, not by these tests.')
    (OUT/'verification.txt').write_text('\n'.join(log)+'\n')
    print('\n'.join(log))

if __name__=='__main__':main()
