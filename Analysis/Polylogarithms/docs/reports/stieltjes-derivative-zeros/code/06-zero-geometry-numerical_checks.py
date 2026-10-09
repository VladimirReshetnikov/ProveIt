#!/usr/bin/env python3
"""High-precision, non-rigorous regression checks; NOT the exact verifier."""
from __future__ import annotations
import json
from pathlib import Path
from math import factorial,comb
import mpmath as mp
from functools import lru_cache

ROOT=Path(__file__).resolve().parents[1]

def elementary(k:int,n:int):
    e=[mp.mpf(1)]+[mp.mpf(0)]*n
    for j in range(1,k+1):
        for i in range(min(j,n),0,-1):e[i]+=e[i-1]/j
    return e

def normalized_master(n:int,k:int,a):
    e=elementary(k,n)
    return sum(mp.factorial(n)/mp.factorial(n-i)*e[i]*
               mp.zeta(k+1,a,derivative=n-i) for i in range(min(n,k)+1))

@lru_cache(maxsize=None)
def zetaconst(j:int):
    return mp.zeta(j)

def appell(n:int,x):
    cumul=[mp.mpf(0),x+mp.euler]
    cumul += [(-1)**(j+1)*mp.factorial(j-1)*zetaconst(j) for j in range(2,n+1)]
    vals=[mp.mpf(1)]
    for j in range(n):
        vals.append(sum(mp.binomial(j,r)*cumul[r+1]*vals[j-r] for r in range(j+1)))
    return vals[n]

def kernel_integral(n:int,k:int,a):
    return mp.quad(lambda t:t**k*mp.exp(-a*t)*appell(n,mp.log(t))/(-mp.expm1(-t)),
                   [0,mp.mpf('.3'),1,3,10,mp.inf])/mp.factorial(k)

def L(s,chi):
    q=len(chi)
    return mp.mpf(q)**(-s)*sum(chi[r]*mp.zeta(s,mp.mpf(r)/q) for r in range(1,q) if chi[r])

def Ld(s,chi,order:int):
    q=mp.mpf(len(chi));lq=mp.log(q)
    return q**(-s)*sum(mp.binomial(order,j)*(-lq)**(order-j)*
        sum(chi[r]*mp.zeta(s,mp.mpf(r)/q,derivative=j)
            for r in range(1,len(chi)) if chi[r]) for j in range(order+1))

def transport_coeffs(k:int,q:int,nu:int,N:int):
    c=[mp.mpf(0),mp.euler+mp.log(2*mp.pi/q)-mp.harmonic(k)]
    for m in range(2,N+1):
        H=sum(mp.mpf(j)**(-m) for j in range(1,k+1))
        if m%2:c.append(mp.factorial(m-1)*(mp.zeta(m)-H))
        else:c.append(mp.factorial(m-1)*(H+(-1)**nu*(1-mp.mpf(2)**(1-m))*mp.zeta(m)))
    out=[mp.mpf(1)]
    for m in range(1,N+1):
        out.append(sum(c[j]*out[m-j]/mp.factorial(j-1) for j in range(1,m+1))/m)
    return out

def scaled_em1(k:int,a,M:int=80,R:int=40):
    """Stable normalized Euler--Maclaurin evaluation, not a certified interval.

    The exact verifier independently encloses the same mathematical quantity.
    Normalization avoids loss from the very small raw Hurwitz-zeta values.
    """
    A=a+M;H=mp.harmonic(k);la=mp.log(A);ratio=(a/A)**(k+1)
    value=sum((H-mp.log(a+m))*(a/(a+m))**(k+1) for m in range(M))
    value+=ratio*(A/k)*(mp.harmonic(k-1)-la)+ratio*(H-la)/2
    prod=mp.mpf(1)
    for j in range(1,2*R):
        prod*=(k+j)/A
        if j%2:
            r=(j+1)//2
            value+=ratio*mp.bernoulli(2*r)/mp.factorial(2*r)*prod*(mp.harmonic(k+j)-la)
    return value

def root1(k:int):
    low=mp.exp(mp.harmonic(k-1))
    return mp.findroot(lambda a:scaled_em1(k,a),(low,low+mp.mpf('.5')))

def main():
    mp.mp.dps=70;checks=[]
    for n in range(4):
        for k in [1,2,5]:
            a=mp.mpf('1.3')
            x=normalized_master(n,k,a);y=kernel_integral(n,k,a)
            err=abs(x-y)/max(1,abs(x))
            assert err<mp.mpf('1e-55')
            checks.append({'kind':'master_vs_laplace','n':n,'k':k,'error':mp.nstr(err,8)})
    print('Laplace checks passed',flush=True)
    chars=[('chi_minus4',[0,1,0,-1]),('chi5',[0,1,-1,-1,1]),
           ('quartic5',[0,1,1j,-1j,-1])]
    for name,cs in chars:
        chi=[mp.mpc(v) for v in cs];bar=[mp.conj(v) for v in chi];q=len(chi)
        for k in [1,2]:
            nu=int(chi[-1]==(-1)**k);N=4
            ds=[Ld(-k,bar,j+nu)/mp.factorial(j+nu) for j in range(N+1)]
            hs=transport_coeffs(k,q,nu,N);lp=L(k+1,chi)
            for m in range(1,N+1):
                predicted=sum(hs[m-j]*(-1)**j*ds[j]/ds[0] for j in range(m+1))
                actual=Ld(k+1,chi,m)/(mp.factorial(m)*lp)
                err=abs(predicted-actual)
                assert err<mp.mpf('1e-50'),(name,k,m,err)
                checks.append({'kind':'jet_transport','character':name,'k':k,'order':m,'error':mp.nstr(err,8)})
            z=mp.mpc('.013','.007')
            trig=(mp.cos(mp.pi*z/2) if nu==0 else mp.sin(mp.pi*z/2)/(mp.pi*z/2))
            actual=mp.rf(1+z,k)*mp.mpf(q)**z*L(k+1+z,chi)/(mp.factorial(k)*lp)
            predicted=(2*mp.pi)**z*mp.rgamma(1+z)/trig*(L(-k-z,bar)/(-z)**nu)/ds[0]
            err=abs(actual-predicted)
            assert err<mp.mpf('1e-50'),(name,k,'universal',err)
            checks.append({'kind':'universal_parity_kernel','character':name,'k':k,'error':mp.nstr(err,8)})
            Y=mp.euler+mp.log(2*mp.pi)
            actual=sum(chi[r]*normalized_master(2,k,mp.mpf(r)/q)
                for r in range(1,q) if chi[r])/(mp.mpf(q)**(k+1)*lp)
            predicted=Y**2+(-1)**nu*mp.zeta(2)/2-2*Y*ds[1]/ds[0]+2*ds[2]/ds[0]
            err=abs(actual-predicted)
            assert err<mp.mpf('1e-50'),(name,k,'coordinate',err)
            checks.append({'kind':'second_index_character_coordinate','character':name,'k':k,'error':mp.nstr(err,8)})
            print(f'Jet and universal-kernel checks passed: {name}, k={k}',flush=True)
    t=mp.exp(-mp.euler);b=1/mp.expm1(t)
    d=1/(2*t)-b
    C=1/(24*t)+t*b*(1+b)-t*t*b*(1+b)*(1+2*b)/2
    rows=[]
    for k in [1,2,5,10,20,50,100,200,500]:
        a=root1(k);approx=k/t+d+C/(k+1)
        rows.append({'k':k,'alpha':mp.nstr(a,60),'linear_error':mp.nstr(a-k/t-d,25),
                     'second_order_error':mp.nstr(a-approx,25),
                     'scaled_second_order_error':mp.nstr((k+1)**2*(a-approx),25)})
    (ROOT/'data/numerical_results.json').write_text(json.dumps({'status':'PASS','precision':mp.mp.dps,
        'checks':checks,'root1_constants':{'t':mp.nstr(t,60),'slope':mp.nstr(1/t,60),'d':mp.nstr(d,60),'C':mp.nstr(C,60)},
        'roots':rows},indent=2)+'\n')
    import csv
    with (ROOT/'data/root1_asymptotics.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=rows[0].keys());w.writeheader();w.writerows(rows)
    print(f'PASS: {len(checks)} high-precision regression checks and {len(rows)} root computations.')

if __name__=='__main__':main()
