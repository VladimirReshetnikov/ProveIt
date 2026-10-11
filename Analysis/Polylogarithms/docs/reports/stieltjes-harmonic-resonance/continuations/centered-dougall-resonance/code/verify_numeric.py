#!/usr/bin/env python3
"""Independent high-precision diagnostics. No interval certification is claimed."""
from __future__ import annotations
import json
import argparse
import platform
import time
from pathlib import Path
from collections import Counter
import mpmath as mp
import sympy as sp
from dougall import (Params,series_jet,closed_resonance_jet,collapsed,half_closed,
                    w_jet,residual_coefficients,zeta_primitive)
ROOT=Path(__file__).resolve().parents[1]
mp.mp.dps=70
rows=[]

def record(group,label,left,right,tolerance='1e-35'):
    err=abs(left-right)/max(mp.mpf(1),abs(right))
    rows.append({'group':group,'label':label,'left':mp.nstr(left,58),'right':mp.nstr(right,58),
                 'scaled_error':mp.nstr(err,15),'tolerance':tolerance})
    assert err<mp.mpf(tolerance),(group,label,mp.nstr(err,10))


def explicit_sums(M,J):
    x0=mp.mpf('0.5'); g=mp.euler
    out=[mp.mpf(0)]*3
    H=mp.mpf(0)
    for n in range(M):
        if n: H+=mp.mpf(1)/n
        x=n+x0
        delta=H-g-mp.log(x)
        out[0]+=delta/x
        out[1]+=((H-g)**2-mp.log(x)**2)/x
        if n:
            out[2]+=-2*n*(n+1)/x*delta+1/(12*x)
        else:
            out[2]+=mp.mpf(1)/6
    d=[mp.mpf(0)]+[-mp.bernpoly(2*j,x0)/(2*j) for j in range(1,J+2)]
    a=M+x0
    for r in range(1,J+1):
        z=mp.zeta(2*r+1,a)
        out[0]+=d[r]*z
        out[1]+=-2*d[r]*mp.zeta(2*r+1,a,derivative=1)
        out[1]+=sum(d[k]*d[r-k] for k in range(1,r))*z
        out[2]+=(-2*d[r+1]+d[r]/2)*z
    return out


def primitive_value(N,b,c,k):
    x=sp.symbols('x')
    bs=sp.Rational(str(b)); cs=sp.Rational(str(c))
    C=(-1)**N*sp.rf(1-bs,N)*sp.rf(1-cs,N)/sp.factorial(N)
    p=sp.expand(C*sp.rf(1+2*x-bs-cs,N))
    q=sp.expand(sp.rf(x-N,N))
    def ev(pol,z):
        return sp.lambdify(x,pol,'mpmath')(z)
    def I(pol,z):
        if pol==0: return mp.mpf(0)
        deg=sp.degree(pol,x)
        return sum((-1)**j*ev(sp.diff(pol,x,j),z)*zeta_primitive(j,z) for j in range(deg+1))
    d0=1+2*k-b-c; y=d0+N
    B=mp.digamma(N+1)-mp.digamma(b)-mp.digamma(c)
    return B*ev(sp.integrate(p,x),k)/2+I(p,k)-mp.mpf(str(C.p))/mp.mpf(str(C.q))*I(q,y)/4


def li_jets_series(z,s,m,count=500):
    out=[mp.mpc(0)]*(m+1)
    zn=z
    for n in range(1,count+1):
        term=zn/n**s; ell=-mp.log(n)
        for r in range(m+1): out[r]+=term*ell**r
        zn*=z
    return out


def shifted_harmonic_sum(a,p,M=100,J=36):
    H=mp.mpf(0); out=mp.mpf(0)
    for n in range(M):
        if n: H+=mp.mpf(1)/n
        out+=(H-mp.euler-mp.log(n+a))/(n+a)**p
    for k in range(1,J+1):
        d=(-1)**(k+1)*mp.bernpoly(k,1-a)/k
        out+=d*mp.zeta(p+k,M+a)
    return out


def shifted_harmonic_closed(a,p):
    if p==1:
        return (mp.zeta(2,a)-mp.digamma(a)**2)/2-mp.stieltjes(1,a)-mp.zeta(2)
    return (mp.digamma(a)*mp.zeta(p,a)+mp.mpf(p)/2*mp.zeta(p+1,a)
            -sum(mp.zeta(j,a)*mp.zeta(p+1-j,a) for j in range(2,p))/2
            +mp.zeta(p,a,derivative=1))


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--part",type=int,choices=[0,1,2],default=0,help="0=all, 1=resonant jets, 2=other identities")
    part=parser.parse_args().part
    start=time.time()
    parameters=[('1/2','1/2','1/2'),('3/4','2/3','4/5'),('5/4','1','3/4'),
                ('2','2','1'),('7/6','1/3','5/7')]
    if part in (0,1):
        for v in parameters:
            p=Params.parse(*v)
            for N in range(4):
                exact=closed_resonance_jet(p,N,3)
                first=series_jet(p,-N,N+1,3,M=80,J=18)
                second=series_jet(p,-N,N+1,3,M=120,J=22)
                label=f'{v}, N={N}'
                for m in range(4):
                    record('Resonant jet: head 80, tail 18',label+f', Taylor order {m}',first[m],exact[m])
                    record('Resonant jet: head 120, tail 22',label+f', Taylor order {m}',second[m],exact[m])
                record('Collapsed constant',label,exact[0],collapsed(p,N),'1e-60')
            print('finished resonances',v,flush=True)
    if part in (0,2):
        for v in parameters[:4]:
            p=Params.parse(*v)
            for N in range(3):
                lhs=series_jet(p,-N-mp.mpf('0.5'),N+1,0,M=100,J=22)[0]
                record('Half-integer resonance',f'{v}, N={N}',lhs,half_closed(p,N))
        print('finished half-integer resonances',flush=True)
        g=mp.euler; L=mp.log(2); A=g+2*L
        explicit=[(mp.zeta(2)-g*g-2*L*L-2*mp.stieltjes(1))/2,
                  A**3/3-A*mp.zeta(2)+mp.mpf(7)/6*mp.zeta(3)-mp.stieltjes(2,mp.mpf('0.5')),
                  mp.zeta(-1,derivative=1)+mp.zeta(2)/4-g*g/4-mp.stieltjes(1)/2-L*L/2+g/12+L/4]
        for M,J in [(100,18),(180,22)]:
            vals=explicit_sums(M,J)
            for j in range(3): record('Printed harmonic identity',f'identity {j+1}, head {M}, tail {J}',vals[j],explicit[j],'1e-48')
        print('finished explicit harmonic sums',flush=True)
        for v in parameters[:2]:
            p=Params.parse(*v)
            for u in [mp.mpf('0.2'),mp.mpf('0'),mp.mpf('-0.5')]:
                z=mp.mpf('0.23'); d=p.d0-u
                top=[2*p.kappa,p.kappa+1,p.b,p.c,d]
                bot=[p.kappa,1+2*p.kappa-p.b,1+2*p.kappa-p.c,p.b+p.c+u]
                w0=w_jet(p,0,u,0)[0]
                for r in [0,1]:
                    if r==0: hyper=w0*mp.hyper(top,bot,z)
                    else: hyper=w0/p.kappa*mp.hyper([2*p.kappa,p.b,p.c,d],bot[1:],z)
                    rhs=hyper-mp.lerchphi(z,1+2*u+r,p.kappa)
                    lhs=residual_coefficients(p,u,1,z,count=150,primitive_order=r)[0]
                    record('Interior subtraction and primitive',f'{v}, u={u}, primitive={r}',lhs,rhs,'1e-55')
        print('finished interior checks',flush=True)
        p=Params.parse('1/2','1/2','1/2')
        record('Zero-head safeguard','W0(-1)=0',w_jet(p,0,-1,1)[0],0,'1e-60')
        record('Zero-head safeguard','W0 prime(-1)=2',w_jet(p,0,-1,1)[1],2,'1e-60')
        z=mp.mpf('0.04')
        for q,pn in [(3,1),(4,3),(5,2),(6,5)]:
            k=mp.mpf(pn)/q; om=mp.exp(2j*mp.pi/q)
            for s in [mp.mpf(-2),mp.mpf('1.3')]:
                alljets=[li_jets_series(om**ell*z**(mp.mpf(1)/q),s,2) for ell in range(q)]
                for m in range(3):
                    lhs=sum(z**n*(-mp.log(n+k))**m/(n+k)**s for n in range(130))
                    rhs=mp.mpc(0)
                    for ell in range(q):
                        jet=sum(mp.binomial(m,r)*mp.log(q)**(m-r)*alljets[ell][r] for r in range(m+1))
                        rhs+=om**(-pn*ell)*jet
                    rhs*=q**(s-1)*z**(-k)
                    record('Root-of-unity spectral filter',f'q={q}, p={pn}, s={s}, order={m}',lhs,rhs,'1e-55')
        print('finished spectral filters',flush=True)
        for N in range(5):
            b=mp.mpf('0.6'); c=mp.mpf('0.7'); k=mp.mpf('0.9')
            lhs=mp.diff(lambda x:primitive_value(N,b,c,x),k)
            record('All-resonance antiderivative',f'N={N}, b=.6,c=.7,k=.9',lhs,collapsed(Params(k,b,c),N),'1e-55')
        print('finished antiderivatives',flush=True)
        for r in range(1,7):
            for n in [0,1,5,20]:
                x=mp.mpf(2)/3
                lhs=mp.polygamma(r-1,n+x)
                rhs=mp.polygamma(r-1,x)+(-1)**(r-1)*mp.factorial(r-1)*sum(1/(j+x)**r for j in range(n))
                record('Harmonic-polygamma conversion',f'r={r}, n={n}',lhs,rhs,'1e-60')
        for a in [mp.mpf('.3'),mp.mpf('.7'),mp.mpf('1'),mp.mpf('1.4')]:
            for p in [1,2,3,4,7]:
                record('Shifted harmonic and Euler-primitive endpoint',f'a={a}, p={p}',
                       shifted_harmonic_sum(a,p),shifted_harmonic_closed(a,p),'1e-48')
        for p in range(2,10):
            right=((2**p-1)*mp.zeta(p,derivative=1)
                   -((2**p-1)*g+(2**p-2)*L)*mp.zeta(p)
                   +mp.mpf(p)/2*(2**(p+1)-1)*mp.zeta(p+1)
                   -sum((2**j-1)*(2**(p+1-j)-1)*mp.zeta(j)*mp.zeta(p+1-j) for j in range(2,p))/2)
            record('Half-parameter Euler-primitive endpoint',f'p={p}',
                   shifted_harmonic_sum(mp.mpf('.5'),p),right,'1e-48')
    groups=Counter(row['group'] for row in rows)
    worst=max(mp.mpf(row['scaled_error']) for row in rows)
    out={'status':'PASS','working_decimal_digits':mp.mp.dps,'total_diagnostics':len(rows),
         'max_scaled_error':mp.nstr(worst,15),'groups':dict(groups),
         'python':platform.python_version(),'mpmath':mp.__version__,'sympy':sp.__version__,
         'elapsed_seconds':round(time.time()-start,2),
         'warning':'Finite asymptotic-tail and floating-point diagnostics; NOT rigorous interval enclosures.',
         'checks':rows}
    destination=ROOT/'results'/('numerical_checks.json' if part==0 else f'numerical_checks_part{part}.json')
    destination.write_text(json.dumps(out,indent=2)+'\n')
    if part and all((ROOT/'results'/f'numerical_checks_part{i}.json').exists() for i in (1,2)):
        inputs=[json.loads((ROOT/'results'/f'numerical_checks_part{i}.json').read_text()) for i in (1,2)]
        combined=dict(out)
        combined['checks']=sum((r['checks'] for r in inputs),[])
        combined['total_diagnostics']=len(combined['checks'])
        combined['elapsed_seconds']=sum(r['elapsed_seconds'] for r in inputs)
        combined['groups']=dict(Counter(row['group'] for row in combined['checks']))
        combined['max_scaled_error']=mp.nstr(max(mp.mpf(row['scaled_error']) for row in combined['checks']),15)
        combined['run_mode']='Two separately executed parts; same assertions as the default full run.'
        (ROOT/'results'/'numerical_checks.json').write_text(json.dumps(combined,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='checks'},indent=2))

if __name__=='__main__': main()
