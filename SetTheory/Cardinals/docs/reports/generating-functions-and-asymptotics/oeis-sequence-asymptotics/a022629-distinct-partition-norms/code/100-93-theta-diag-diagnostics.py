#!/usr/bin/env python3
"""Critical growing-power diagnostics. NOT exact integer coefficient counts.

Reproducible extended-precision discrete Bernoulli Fourier quadrature.
Uses exact integer deterministic baselines, retains part 1 in S but not R.
Polynomial-in-local-Fourier-coordinate integration is cross-checked directly.
"""
import os, json, math, argparse, time
from fractions import Fraction
import numpy as np
from scipy.optimize import brentq
from scipy.integrate import quad
from numpy.polynomial.legendre import leggauss
import mpmath as mp
LD=np.longdouble; CD=np.clongdouble
PI=np.arccos(LD(-1)); TWOPI=2*PI

def root_K(a,lam):
    mp.mp.dps=65
    b=mp.findroot(lambda b:a*(b-1)*mp.exp(-b/3)-lam,(8,30),solver='anderson') if False else mp.findroot(lambda b:a*(b-1)*mp.exp(-b/3)-lam, (mp.mpf(brentq(lambda b:a*(b-1)*math.exp(-b/3)-lam,4,100))-.1,mp.mpf(brentq(lambda b:a*(b-1)*math.exp(-b/3)-lam,4,100))+.1))
    return LD(str(mp.exp(b)))

def build(a,K,B=85):
    a=LD(a);K=LD(K); b=np.log(K);t=a*b/K; W=K/(a*(b-1));m=int(np.floor(K))
    # On the frozen interval f(k)>=B by concavity; endpoints found explicitly.
    peak=K/b
    fp=a*np.log(peak)-t*peak
    if fp>B:
        lo=2 if a*np.log(LD(2))-t*2>=B else int(math.ceil(brentq(lambda x:float(a*np.log(LD(x))-t*x-B),2,float(peak))))
        hi=int(math.floor(brentq(lambda x:float(a*np.log(LD(x))-t*x-B),float(peak),float(K))))
        while a*np.log(LD(lo))-t*lo<B: lo+=1
        while a*np.log(LD(hi))-t*hi<B: hi-=1
        ks=np.concatenate((np.arange(2,lo,dtype=np.int64),np.arange(hi+1,m+1,dtype=np.int64)))
        frozen=max(0,hi-lo+1)
    else:
        ks=np.arange(2,m+1,dtype=np.int64);frozen=0
    # f is decreasing past K; this geometric bound controls all omitted upper k.
    upper=int(math.ceil(brentq(lambda x:float(a*np.log(LD(x))-t*x+B),float(K),float(K+4*(B+5)*W))))
    ks=np.concatenate((ks,np.arange(m+1,upper+1,dtype=np.int64)))
    k=ks.astype(LD); f=a*np.log(k)-t*k
    h=np.where(ks<=m,LD(-1),LD(1));q=1/(1+np.exp(np.abs(f)))
    v=q*(1-q);d=k-K;p1=1/(1+np.exp(t));v1=p1*(1-p1)
    corrR=np.sum(h*q,dtype=LD)
    corrS=np.sum(h*k*q,dtype=LD)+p1
    baseS=m*(m+1)//2-1; baseR=m-1
    U=np.sum(v,dtype=LD);T1=np.sum(d*v,dtype=LD);T2=np.sum(d*d*v,dtype=LD)
    C=K*U+T1;V=K*K*U+2*K*T1+T2+v1
    Q=(U*T2-T1*T1+U*v1)/V
    # Do not collapse baseline+correction when selecting integer n.
    nint=baseS+int(np.floor(corrS+LD('.5')))
    mean_resid=LD(baseS-nint)+corrS
    omitted=frozen*np.exp(-LD(B))+np.exp(a*np.log(LD(upper+1))-t*(upper+1))/(1-np.exp(-1/W))
    return dict(a=int(a),K=K,b=b,t=t,W=W,k=k,ks=ks,h=h,q=q,p1=p1,U=U,T1=T1,T2=T2,C=C,V=V,Q=Q,baseS=baseS,baseR=baseR,corrS=corrS,corrR=corrR,n=nint,mean_resid=mean_resid,frozen=frozen,upper=upper,omitted=omitted)

def select_case(a,lam,phase,B=85):
    K0=root_K(a,lam); s=build(a,K0,B)
    # Closest integer/half-integer of ER at the reference critical saddle.
    target_int=s['baseR']+int(np.floor(s['corrR']-LD(phase)+LD('.5')))
    target_frac=LD(str(phase))
    K=K0
    for z in range(12):
        s=build(a,K,B)
        resid=LD(s['baseR']-target_int)+s['corrR']-target_frac
        deriv=s['C']/(K*s['W'])
        K-=resid/deriv
        if abs(resid)<LD('1e-12'):break
    real_s=build(a,K,B);n=real_s['n'];n_round_delta=-real_s['mean_resid']
    for z in range(12):
        s=build(a,K,B)
        resid=LD(s['baseS']-n)+s['corrS']
        K-=resid*K*s['W']/s['V']
        if abs(resid)<LD('2e-12'):break
    s=build(a,K,B);s['n']=n;s['mean_resid']=LD(s['baseS']-n)+s['corrS']
    s.update(lam_target=lam,phase_target=phase,K_reference=K0,phase_target_int=target_int,n_round_delta=n_round_delta)
    return s

def theta(mu,Q):
    return np.sum(np.exp(-(np.arange(-20,21,dtype=LD)-mu)**2/(2*Q)),dtype=LD)/np.sqrt(2*PI*Q)

def cumulant_polynomials(order):
    ps=[None,[Fraction(0),Fraction(1)]]
    for r in range(1,order):
        p=ps[-1];out=[Fraction(0)]*(len(p)+1)
        for j in range(1,len(p)):
            out[j]+=p[j]*j/Fraction(r+1);out[j+1]-=p[j]*j/Fraction(r+1)
        ps.append(out)
    return [None]+[np.array([LD(p.numerator)/LD(p.denominator) for p in row],dtype=LD) for row in ps[1:]]

def characteristic(s,j,y):
    th=TWOPI*j*s['C']/s['V']+LD(y)/np.sqrt(s['V'])
    alpha=th*s['k']-TWOPI*j
    beta=s['h']*alpha
    terms=np.log1p(s['q']*np.expm1(1j*beta))-1j*s['q']*beta
    one=np.log1p(s['p1']*np.expm1(1j*th))-1j*s['p1']*th
    mu=np.remainder(s['corrR'],1)
    return np.exp(np.sum(terms,dtype=CD)+one-1j*TWOPI*j*mu+1j*th*s['mean_resid'])

def expansion(s,j,order,polys):
    th=TWOPI*j*s['C']/s['V'];rootV=np.sqrt(s['V'])
    alpha=th*s['k']-TWOPI*j;beta=s['h']*alpha
    q=s['q'];h=s['h'];k=s['k']
    ee=np.exp(1j*beta);z=q*ee/(1+q*np.expm1(1j*beta))
    d=1j*h*k/rootV
    p=s['p1'];z1=p*np.exp(1j*th)/(1+p*np.expm1(1j*th));d1=1j/rootV
    mu=np.remainder(s['corrR'],1)
    coeff=[np.sum(np.log1p(q*np.expm1(1j*beta))-1j*q*beta,dtype=CD)+np.log1p(p*np.expm1(1j*th))-1j*p*th-1j*TWOPI*j*mu+1j*th*s['mean_resid']]
    coeff.append(np.sum(d*(z-q),dtype=CD)+d1*(z1-p)+1j*s['mean_resid']/rootV)
    dp=d.copy();dp1=d1
    for r in range(2,order+1):
        dp*=d;dp1*=d1
        cr=np.polynomial.polynomial.polyval(z,polys[r]);cr1=np.polynomial.polynomial.polyval(z1,polys[r])
        coeff.append(np.sum(dp*cr,dtype=CD)+dp1*cr1)
    return np.array(coeff,dtype=CD)

def quadrature(s,J,order=30,Y=11,N=160,direct=False):
    xx,ww=leggauss(N);ys=xx.astype(LD)*LD(Y);ws=ww.astype(LD)*LD(Y)
    polys=cumulant_polynomials(order)
    ans=LD(0);sat=[];maxpoint=0.;errs=[]
    for j in range(J+1):
        if direct:
            phis=np.array([characteristic(s,j,y) for y in ys]);value=np.sum(ws*phis,dtype=CD)/np.sqrt(2*PI)
        else:
            cs=expansion(s,j,order,polys)
            phis=np.exp(np.polynomial.polynomial.polyval(ys,cs))
            value=np.sum(ws*phis,dtype=CD)/np.sqrt(2*PI)
            # Independent exact-product checks, including oscillatory/noncentral points.
            for y in [-8,-4,0,4,8]:
                got=np.exp(np.polynomial.polynomial.polyval(LD(y),cs));want=characteristic(s,j,LD(y))
                maxpoint=max(maxpoint,float(abs(got-want)))
            # Integrate several Taylor orders using the same full discrete cumulants.
            ordvals=[]
            for oo in [16,20,24,order]:
                val=np.sum(ws*np.exp(np.polynomial.polynomial.polyval(ys,cs[:oo+1])),dtype=CD)/np.sqrt(2*PI)
                ordvals.append(val)
            errs.append([float(abs(x-value)) for x in ordvals])
        sat.append(dict(j=j,re=float(value.real),im=float(value.imag)))
        ans+=(1 if j==0 else 2)*value.real
    return ans,dict(satellites=sat,taylor_order=order,Y=Y,N=N,max_exact_product_point_error=maxpoint,taylor_order_comparison_errors=errs)

def clean(s):
    out={}
    for k,v in s.items():
        if isinstance(v,np.ndarray):continue
        if isinstance(v,(LD,CD)):out[k]=str(v)
        else:out[k]=v
    out['mu_fraction']=str(np.remainder(s['corrR'],1))
    out['mu_minus_target']=str(LD(s['baseR']-s['phase_target_int'])+s['corrR']-LD(s['phase_target']))
    out['actual_lambda']=str(s['a']*(s['b']-1)/s['K']**(LD(1)/3))
    out['Q_limit']=str(PI**2/(3*LD(s['lam_target'])**3))
    out['active_count']=len(s['k'])
    return out

def run(args):
    rows=[];start=time.time()
    for lam in args.lambdas:
        for a in args.powers:
            for phase in args.phases:
                s=select_case(a,lam,phase,args.cutoff)
                J=8 if lam==4 else 10
                M,diag=quadrature(s,J,args.order,args.window,args.nodes,args.direct)
                mu=np.remainder(s['corrR'],1);T=theta(mu,s['Q']);out=clean(s)
                out.update(multiplier=str(M),theta_exact_moments=str(T),theta_limit=str(theta(LD(str(phase)),PI**2/(3*LD(lam)**3))),relative_theta_error=str(M/T-1),single_gaussian_relative_error=str(1/M-1),quadrature=diag,wall_seconds=time.time()-start)
                rows.append(out);print(json.dumps({k:out[k] for k in ['a','lam_target','phase_target','n','mu_minus_target','Q','multiplier','theta_exact_moments','relative_theta_error','active_count','wall_seconds']}),flush=True)
                with open(args.output,'w') as f:json.dump({'method':'Extended-precision Fourier quadrature, not exact integer coefficient DP','rigorous':False,'longdouble_bits':np.finfo(LD).nmant+1,'rows':rows},f,indent=2)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--powers',type=int,nargs='+',default=[12,20,32,48]);ap.add_argument('--lambdas',type=int,nargs='+',default=[4,5]);ap.add_argument('--phases',type=float,nargs='+',default=[0,.5]);ap.add_argument('--order',type=int,default=30);ap.add_argument('--nodes',type=int,default=160);ap.add_argument('--window',type=float,default=11);ap.add_argument('--cutoff',type=int,default=85);ap.add_argument('--direct',action='store_true');ap.add_argument('--output',default=os.path.join(os.path.dirname(__file__),'results.json'));run(ap.parse_args())
