#!/usr/bin/env python3
"""Finite exact algebra and non-interval diagnostics for polylog order filters.
The order-zero reference is an endpoint-subtracted Fermi integral, NOT tiny-step
numerical differentiation of polylog. No network requests are made.
"""
from __future__ import annotations
import argparse, json, math, platform, time
from pathlib import Path
from typing import Callable
import mpmath as mp
import sympy as sp
U=sp.Symbol('u',real=True)
P=sp.Symbol('p',positive=True)


def trig(poly: sp.Expr, kind: str) -> sp.Expr:
    poly=sp.expand(poly)
    if poly==0: return sp.Integer(0)
    d=int(sp.degree(poly,U));start=0 if kind=='cos' else 1
    return sp.expand(sum((-1)**((j-start)//2)*P**j*sp.diff(poly,U,j)/sp.factorial(j)
                         for j in range(start,d+1,2)))


def invert(target: sp.Expr, kind: str, normalize: bool=False) -> sp.Expr:
    residual,out=sp.expand(target),sp.Integer(0)
    for k in range(int(sp.degree(target,U)),-1,-1):
        c=sp.expand(residual).coeff(U,k)
        term=c*U**k if kind=='cos' else c*U**(k+1)/(P*(k+1))
        out+=term;residual=sp.expand(residual-trig(term,kind))
    if sp.simplify(residual)!=0: raise ArithmeticError('operator inversion')
    if normalize: out+=1-trig(out,'cos').subs(U,0)
    return sp.expand(out)


def bells(values: list, nmax: int) -> list:
    out=[mp.mpf(1)]
    for n in range(nmax):
        out.append(mp.fsum(math.comb(n,j)*out[n-j]*values[j] for j in range(n+1)))
    return out


def cauchy(f: Callable, radius: mp.mpf, degree: int, samples: int) -> list:
    vals=[f(radius*mp.exp(2j*mp.pi*k/samples)) for k in range(samples)]
    return [mp.fsum(vals[k]*mp.exp(-2j*mp.pi*k*r/samples) for k in range(samples))
            /(samples*radius**r) for r in range(degree+1)]


def tail(q, r: int, order=0):
    if abs(q)>=1: raise ValueError('tail requires |q|<1')
    if q==0: return mp.mpf(0)
    nmax=max(40,int((mp.mp.dps+25)*mp.log(10)/(-mp.log(abs(q))))+20)
    return mp.fsum((-1)**(n-1)*(-mp.log(n))**r*q**n/mp.power(n,order)
                   for n in range(1,nmax+1))


def A(z):
    return mp.euler+mp.log(2*mp.pi)+(mp.digamma(mp.mpf('.5')+1j*z/(2*mp.pi))
                         +mp.digamma(mp.mpf('.5')-1j*z/(2*mp.pi)))/2


def Ad(z,k: int):
    return mp.re(((1j/(2*mp.pi))**k*mp.polygamma(k,mp.mpf('.5')+1j*z/(2*mp.pi))
                  +(-1j/(2*mp.pi))**k*mp.polygamma(k,mp.mpf('.5')-1j*z/(2*mp.pi)))/2)


def integral_jets(x,degree: int):
    f0=1/(1+mp.exp(-x))
    points=sorted(set([mp.mpf(0),mp.mpf(1),max(mp.mpf(2),x),max(mp.mpf(8),x+8)]))
    moments=[]
    for j in range(degree):
        def f(t):
            if t==0: return mp.mpf(0) # endpoint value is irrelevant to integral
            return f0*(-mp.expm1(-t))*mp.log(t)**j/(t*(1+mp.exp(t-x)))
        moments.append(mp.quad(f,points+[mp.inf]))
    g=[mp.euler]+[(-1)**(j+1)*mp.factorial(j-1)*mp.zeta(j) for j in range(2,degree+1)]
    eb=bells(g,degree)
    return [f0]+[r*mp.fsum(math.comb(r-1,j)*eb[r-1-j]*moments[j] for j in range(r))
                 for r in range(1,degree+1)]


def serial(x):
    if isinstance(x,dict): return {str(k):serial(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)): return [serial(v) for v in x]
    if isinstance(x,mp.mpc): return {'re':mp.nstr(x.real,48),'im':mp.nstr(x.imag,48)}
    if isinstance(x,mp.mpf): return mp.nstr(x,48)
    return x


class Checks:
    def __init__(self): self.exact=0; self.numerical=[]
    def eq(self,a,b=0):
        if sp.simplify(sp.expand(a-b))!=0: raise AssertionError(f'{a} != {b}')
        self.exact+=1
    def near(self,label,a,b,tol):
        err=abs(a-b)
        self.numerical.append({'label':label,'absolute_error':err,'tolerance':tol})
        if not err<tol: raise AssertionError(f'{label}: {err} >= {tol}')


def exact_checks(ch: Checks):
    for d in range(1,11):
        poly=sum(sp.Rational((j+1)*(-1)**j,j+2)*U**j for j in range(d+1))
        re,im=trig(poly,'cos'),trig(poly,'sin')
        ch.eq(poly.subs(U,U+sp.I*P),re+sp.I*im)
        ch.eq(invert(re,'cos'),poly)
        ch.eq(trig(invert(im,'sin'),'sin'),im)
        ch.eq(sp.Poly(im,U).LC(),P*d*sp.Poly(poly,U).LC())
        ch.eq(sp.degree(im,U),d-1);ch.eq(sp.degree(re,U),d)
        C=sp.Matrix([[trig(U**j,'cos').coeff(U,i) for j in range(d+1)] for i in range(d+1)])
        S=sp.Matrix([[trig(U**j,'sin').coeff(U,i) for j in range(d+1)] for i in range(d+1)])
        ch.eq(C.det(),1);ch.eq(S.rank(),d);ch.eq((C-sp.sqrt(3)*S).det(),1)
    polys={}
    for N in range(1,7):
        Q=sp.prod(U+j for j in range(N));filt=invert(Q,'sin',True)
        ch.eq(trig(filt,'sin'),Q);ch.eq(trig(filt,'cos').subs(U,0),1)
        comp=sp.prod(U+j for j in range(N+1))
        ch.eq(trig(invert(comp,'cos'),'cos'),comp)
        joint=sp.prod((U+j)**2+P**2 for j in range(N))
        for j in range(N):
            ch.eq(joint.subs(U,-j+sp.I*P));ch.eq(joint.subs(U,-j-sp.I*P))
        nodes=[-sp.Rational(j)+s*sp.I for j in range(N) for s in [-1,1]]
        V=sp.Matrix([[z**k for k in range(2*N)] for z in nodes])
        if V.det()==0: raise AssertionError('Vandermonde determinant')
        ch.exact+=1
    for N in range(1,4):
        Q=sp.prod(U+sp.log(j) for j in range(1,N+1));Pi=invert(Q,'sin',True)
        ch.eq(trig(Pi,'sin'),Q);ch.eq(trig(Pi,'cos').subs(U,0),1)
        polys[str(N)]={'Pi':str(Pi.subs(P,sp.pi)),
                       'R':str(trig(Pi,'cos').subs(P,sp.pi)),'Q':str(Q)}
    q,c,a,b=sp.symbols('q c a b',nonzero=True)
    d1=-c/a;d2=-b*c*c/(2*a**3)-c*c/a**2+c/a;delta=d1*q+d2*q*q
    res=a*delta+b*delta**2/2+c*(q*(1-delta)-q*q)
    ch.eq(sp.expand(res).coeff(q,1));ch.eq(sp.expand(res).coeff(q,2))
    ch.eq((d2.subs(c,sp.I*P)+d2.subs(c,-sp.I*P))/2,P**2/a**2+P**2*b/(2*a**3))
    return polys


def stieltjes_checks(ch: Checks,tol):
    rows=[]
    for x in map(mp.mpf,['1.3','3']):
        az=mp.mpf('.5')+1j*x/(2*mp.pi)
        fn=lambda s:mp.zeta(1-s,az)+1/s
        c96=cauchy(fn,mp.mpf('.22'),3,96);c64=cauchy(fn,mp.mpf('.22'),3,64)
        gamma=[mp.factorial(j)*c96[j] for j in range(4)]
        for j in range(4): ch.near(f'Cauchy refinement x={x} j={j}',c96[j],c64[j],tol)
        ch.near(f'gamma0 x={x}',gamma[0],-mp.digamma(az),tol)
        ds=[mp.euler+mp.log(2*mp.pi)-.5j*mp.pi]+[
            (-1)**(j+1)*mp.factorial(j-1)*mp.zeta(j) for j in range(2,5)]
        eb=bells(ds,4);refs=integral_jets(x,4)
        for r in range(1,5):
            L=eb[r]-r*mp.fsum(math.comb(r-1,j)*gamma[j]*eb[r-1-j] for j in range(r))
            T=mp.fsum(math.comb(r,j)*(-1j*mp.pi)**j*tail(mp.exp(-x),r-j) for j in range(r+1))
            ch.near(f'zero jet r={r} x={x}',L-T,refs[r],tol)
            rows.append({'x':x,'r':r,'jet':refs[r],'error':abs(L-T-refs[r])})
        ch.near(f'digamma H x={x}',A(x)-tail(mp.exp(-x),1),refs[1],tol)
    return rows


def borel_checks(ch: Checks,tol):
    rows=[]
    for x,theta in [(mp.mpf('1.3'),mp.mpf('.45')),(mp.mpf('3'),mp.mpf('.6'))]:
        ray=mp.exp(1j*theta)
        def f(t):
            z=ray*t
            if abs(z)<mp.mpf('1e-18'):
                minor=-mp.pi**2*z/6-7*mp.pi**4*z**3/360
            else: minor=1/z-mp.pi/mp.sin(mp.pi*z)
            return ray*mp.exp(-x*z)*minor
        val=mp.quad(f,[0,1,3,8,20,mp.inf])
        target=mp.digamma(mp.mpf('.5')+1j*x/(2*mp.pi))-mp.log(x)+mp.log(2*mp.pi)-.5j*mp.pi
        ch.near(f'Borel x={x}',val,target,tol)
        rows.append({'x':x,'theta':theta,'error':abs(val-target)})
    for s,x in [(mp.mpc('.3','.2'),mp.mpf('1.3')),(mp.mpf('1.7'),mp.mpf('3')),
                (mp.mpf('-.2'),mp.mpf('1.3'))]:
        F=-mp.polylog(s,-mp.exp(x));T=-mp.polylog(s,-mp.exp(-x))
        az=mp.mpf('.5')+1j*x/(2*mp.pi)
        L=-(2*mp.pi)**s*mp.exp(-.5j*mp.pi*s)*mp.rgamma(s)*mp.zeta(1-s,az)
        ch.near(f'Jonquiere s={s} x={x}',L,F+mp.exp(-1j*mp.pi*s)*T,tol)
        rows.append({'s':s,'x':x,'error':abs(L-F-mp.exp(-1j*mp.pi*s)*T)})
    return rows


def neutral_checks(ch: Checks,tol):
    rows=[]
    for N in [1,2,3]:
        Q=sp.prod(U+sp.log(j) for j in range(1,N+1));Pi=invert(Q,'sin',True)
        R=sp.lambdify(U,trig(Pi,'cos').subs(P,sp.pi),'mpmath');m=1
        kappa=mp.fprod(mp.log(mp.mpf(N+1)/j) for j in range(1,N+1))/(N+1)**m
        for q in map(mp.mpf,['.01','.001']):
            terms=max(45,int((mp.mp.dps+20)*mp.log(10)/(-mp.log(q)))+10)
            nodes=[-mp.log(n) for n in range(1,terms+1)];rv=[R(u) for u in nodes]
            iv=[mp.mpf(0) if n<=N else mp.fprod(nodes[n-1]+mp.log(j) for j in range(1,N+1))
                for n in range(1,terms+1)]
            def psi(eps):
                return mp.fsum((-1)**(n-1)*mp.power(n,-m-eps)*q**(n-1)*
                    (mp.sin(mp.pi*eps)*rv[n-1]+mp.cos(mp.pi*eps)*iv[n-1])
                    for n in range(1,terms+1))
            eps=mp.findroot(psi,(-kappa*q**N/mp.pi,mp.mpf(0)),solver='secant',
                            tol=mp.mpf(10)**(-mp.mp.dps+8))
            ch.near(f'neutral N={N} q={q}',psi(eps),0,tol)
            cscaled=mp.fsum((-1)**(n-1)*mp.power(n,-m-eps)*q**(n-1)*
                (mp.cos(mp.pi*eps)*rv[n-1]-mp.sin(mp.pi*eps)*iv[n-1])
                for n in range(1,terms+1))
            rows.append({'N':N,'m':m,'q':q,'epsilon':eps,
                'epsilon_over_leading':eps/(-kappa*q**N/mp.pi),
                'completion_over_signed_q':cscaled,'residual':abs(psi(eps))})
    return rows


def large_inverse_checks(ch: Checks,tol):
    rows=[]
    for w in map(mp.mpf,['5','8','12','20','35']):
        y=mp.re(A(w));q=mp.exp(-w);a=Ad(w,1);b=Ad(w,2)
        H=lambda z:A(z)-tail(mp.exp(-z),1)
        X=mp.findroot(lambda z:H(z)-y,(w,w+mp.mpf('.001')),tol=mp.mpf(10)**(-mp.mp.dps+8))
        def lat(z):
            qq=mp.exp(-z);return A(z)-1j*mp.pi*qq/(1+qq)
        G=mp.findroot(lambda z:lat(z)-y,(w,w+1j*mp.mpf('.001')),
                      tol=mp.mpf(10)**(-mp.mp.dps+8))
        ch.near(f'physical inverse residual w={w}',H(X),y,tol)
        ch.near(f'lateral inverse residual w={w}',lat(G),y,tol)
        pred=(mp.pi**2/a**2+mp.pi**2*b/(2*a**3)-mp.log(2)/a)*q*q
        rows.append({'w':w,'y':y,'X_minus_w':mp.re(X-w),
             'physical_scaled':mp.re(X-w)/(w*q*q),
             'defect':mp.re(G-X),'defect_scaled':mp.re(G-X)/(w*w*q*q),
             'defect_over_second_order':mp.re(G-X)/pred,
             'lateral_imag_scaled':mp.im(G)/(w*q)})
    return rows


def small_inverse_checks(ch: Checks,tol):
    # Polynomial convolutions instead of costly general symbolic expansion.
    deg=6;bb=[mp.mpf(1)]+[(-1)**(j+2)*mp.log(j+2)/mp.log(2) for j in range(1,deg+1)]
    def mul(a,b):
        return [mp.fsum(a[k]*b[n-k] for k in range(n+1)) for n in range(deg+1)]
    c=[];v=[mp.mpf(0)]+bb[1:]
    for N in range(1,deg+1):
        power=[mp.mpf(1)]+[mp.mpf(0)]*deg;value=mp.mpf(0)
        for j in range(N+1):
            value+=mp.binomial(-mp.mpf(N)/2,j)*power[N]
            power=mul(power,v)
        c.append(value/N)
    ch.near('small coefficient 1',c[0],mp.log(3)/(2*mp.log(2)),tol)
    ch.near('small coefficient 2',c[1],mp.log(3)**2/(2*mp.log(2)**2)-1,tol)
    rows=[]
    for t in map(mp.mpf,['.01','.003','.001']):
        y=mp.log(2)*t*t
        zroot=mp.findroot(lambda z:tail(z,1)-y,(t,t*mp.mpf('1.01')),
                          tol=mp.mpf(10)**(-mp.mp.dps+8))
        x=mp.log(zroot);approx=mp.log(t)+mp.fsum(c[N-1]*t**N for N in range(1,7))
        ch.near(f'small inverse residual t={t}',tail(zroot,1),y,tol)
        rows.append({'t':t,'y':y,'x':x,'six_term_error':abs(x-approx),
                     'error_over_t7':abs(x-approx)/t**7})
    return {'coefficients':c,'cases':rows}


GROUPS={'exact':exact_checks,'stieltjes':stieltjes_checks,'borel':borel_checks,
        'neutral':neutral_checks,'large_inverse':large_inverse_checks,'small_inverse':small_inverse_checks}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output-dir',type=Path,default=Path('replay'))
    ap.add_argument('--dps',type=int,default=70)
    ap.add_argument('--group',choices=['all']+list(GROUPS),default='all')
    ap.add_argument('--overwrite',action='store_true');args=ap.parse_args()
    if args.dps<50: ap.error('--dps must be >=50')
    args.output_dir.mkdir(parents=True,exist_ok=True);mp.mp.dps=args.dps
    selected=list(GROUPS) if args.group=='all' else [args.group]
    for group in selected:
        path=args.output_dir/(group+'.json')
        if path.exists() and not args.overwrite: ap.error(f'{path} exists; select a new output directory')
        started=time.time();ch=Checks();print(group,flush=True)
        tol=mp.mpf('1e-45') if args.dps>=60 else mp.mpf('1e-32')
        result=GROUPS[group](ch) if group=='exact' else GROUPS[group](ch,tol)
        report={'status':'PASS','group':group,
                'evidence_scope':'finite exact algebra / non-interval numerical diagnostics',
                'python':platform.python_version(),'mpmath':mp.__version__,'sympy':sp.__version__,
                'dps':args.dps,'exact_assertions':ch.exact,'numerical_assertions':len(ch.numerical),
                'elapsed_seconds':round(time.time()-started,3),'checks':ch.numerical,'results':result}
        path.write_text(json.dumps(serial(report),indent=2)+'\n',encoding='utf-8')
        print(f'PASS {ch.exact} exact / {len(ch.numerical)} numerical, {time.time()-started:.1f}s',flush=True)

if __name__=='__main__': main()
