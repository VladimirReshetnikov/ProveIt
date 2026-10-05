#!/usr/bin/env python3
"""Reproducible numerical diagnostics (not rigorous interval certificates)."""
from __future__ import annotations
import json
from pathlib import Path
import mpmath as mp
from verify import coefficients

mp.mp.dps = 65
J = 320
OUT = Path(__file__).resolve().parent.parent/'data'


def ud(q, j=1, cap=J):
    U=D=mp.mpf('0')
    for k in range(cap,j-1,-1):
        p=q**k
        unext=U
        U=p/(1-p)+U/(1-p)**2
        D=p/(1-p)+D/((1-p)**2*(1-p*unext/(1-p)))
    return U,D


def K(q,j=1,cap=J):
    return q**j/(1-q**j)*ud(q,j+1,cap)[0]


def root(j):
    lo,hi=mp.mpf('0.1'),mp.mpf('0.9')
    for _ in range(235):
        mid=(lo+hi)/2
        if K(mid,j)<1: lo=mid
        else: hi=mid
    return (lo+hi)/2


def moment(q,j=1):
    val=K(q,j)
    m=q*mp.diff(lambda x:K(x,j),q)/val
    v=(q*q*mp.diff(lambda x:K(x,j),q,2)+q*mp.diff(lambda x:K(x,j),q))/val-m*m
    return m,v


def fmt(x): return mp.nstr(x,40)


def run():
    rho,R=root(1),root(2)
    m,v=moment(rho)
    P=mp.exp(-2*mp.fsum(mp.log(1-rho**j) for j in range(1,J+1)))
    A=P*rho*rho/m
    d_a=2+2*mp.fsum(j*rho**j/(1-rho**j) for j in range(1,J+1))
    uc=1/K(R)
    M,V=moment(R)
    Kc2=uc*R*R*mp.diff(lambda q:K(q),R,2)/2
    E2=lambda q:ud(q,3)[1]/(1-q*q)**2
    M2,V2=moment(R,2)
    J2=R*R*mp.diff(lambda q:K(q,2),R,2)/2
    c2=E2(R)/M2
    d20=R*R/(1-R*R)+E2(R)*J2/M2**2-R*mp.diff(E2,R)/M2
    b=c2/(1-R)**2
    b0=d20/(1-R)**2-2*R*c2/(1-R)**3
    kap=b/M
    kap0=kap+b0/M+b*Kc2/M**2
    d=b*(-mp.mpf('0.5')+1/M+Kc2/M**2)+b0/M
    D=V/(2*M**3)
    constants=dict(rho=rho,R=R,uc=uc,physical_M=m,physical_V=v,
                   physical_mu=1/m,physical_sigma2=v/m**3,
                   P=P,A=A,log_height_scale=1/mp.log(1/rho),
                   critical_M=M,critical_V=V,critical_mu=1/M,
                   critical_mean_density=1/(2*M),
                   critical_variance_density=1/(12*M*M),
                   b=b,b0=b0,Jc=Kc2,kappa=kap,kappa0=kap0,
                   shift=kap0/kap,critical_D=D,critical_d=d)
    P_at_R=mp.exp(-2*mp.fsum(mp.log(1-R**k) for k in range(1,J+1)))
    P3_at_R=P_at_R*(1-R)**2*(1-R**2)**2
    constants.update(
        critical_height_alpha1=uc*R**2*P_at_R/M,
        critical_height_alpha2=R**3*P3_at_R/((1-R**2)*(1-R)*M2),
        critical_level2_M=M2,
        critical_height_scale=1/mp.log(1/R))
    assert abs(uc-R*(1-R)*(1-R*R)/(1+R**4))<mp.mpf('1e-55')
    # Agreement of two truncation depths, not an interval enclosure.
    tail_agreement=abs(K(R,1,220)-K(R,1,320))
    payload=json.loads((OUT/'exact_checks.json').read_text())
    nmax=len(payload['D1'])-1
    u2=[int(x) for x in payload['U2']]
    d2=[int(x) for x in payload['D2']]
    dn=[int(x) for x in payload['D1']]
    # Coefficients of K=q/(1-q)U2 and B=D2/(1-q)^2.
    kc=[0]*(nmax+1); bc=[0]*(nmax+1)
    for n in range(1,nmax+1):
        kc[n]=kc[n-1]+u2[n-1]
        bc[n]=sum((n-i+1)*d2[i] for i in range(n+1))
    ks=[mp.mpf(kc[i])*R**i for i in range(nmax+1)]
    bs=[mp.mpf(bc[i])*R**i for i in range(nmax+1)]
    def scaled_coeffs(u, moments=False):
        f=[mp.mpf(0)]*(nmax+1)
        f1=f[:]; f2=f[:]
        for n in range(1,nmax+1):
            f[n]=bs[n]+u*mp.fsum(ks[k]*f[n-k] for k in range(3,n+1))
            if moments:
                f1[n]=u*mp.fsum(ks[k]*(f[n-k]+f1[n-k]) for k in range(3,n+1))
                f2[n]=u*mp.fsum(ks[k]*(2*f1[n-k]+f2[n-k]) for k in range(3,n+1))
        for n in range(1,nmax+1): f[n]+=R**n
        return f,f1,f2
    f,f1,f2=scaled_coeffs(uc,True)
    critical=[]
    for n in [30,60,120,240]:
        if n>nmax:continue
        mean=f1[n]/f[n]
        var=(f2[n]+f1[n])/f[n]-mean**2
        critical.append({'n':n,'scaled_count':fmt(f[n]),
                         'two_term_residual':fmt(f[n]-kap*n-kap0),
                         'mean_over_n':fmt(mean/n),'var_over_n2':fmt(var/n**2)})
    windows=[]
    for s in [-4,0,4]:
        n=min(240,nmax); z=mp.mpf(s)/M
        if s: fw,_,_=scaled_coeffs(uc*mp.exp(mp.mpf(s)/n))
        else:fw=f
        G=mp.expm1(z)/z if s else mp.mpf(1)
        C0=b/2+mp.exp(z)*(d+b*D*s)
        windows.append({'n':n,'s':s,'scaled_exact':fmt(fw[n]),
                        'leading':fmt(kap*n*G),
                        'two_term':fmt(kap*n*G+C0),
                        'two_term_error':fmt(fw[n]-kap*n*G-C0)})
    heights=[]
    for n in [60,120,240]:
        if n>nmax:continue
        center=int(mp.floor(mp.log(A*n)/mp.log(1/rho)))
        for h in [center-1,center,center+1]:
            _,capped=coefficients(n,cap=h)
            exact=mp.mpf(capped[n])/dn[n]
            pred=mp.exp(-A*n*rho**h)
            heights.append({'n':n,'h':h,'exact_cdf':fmt(exact),
                            'limit_cdf':fmt(pred),'difference':fmt(exact-pred)})
    shifts=[]
    for h in [8,12,16,24,32]:
        rr=mp.findroot(lambda q:K(q,1,h)-1,(rho,rho+mp.mpf('.001')))
        delta=mp.log(rr/rho); eps=rho**h
        p2=A*A*(h+d_a-(m*m+v)/(2*m))-A*rho/(1-rho)
        approx1=A*eps; approx2=approx1+p2*eps*eps
        shifts.append({'h':h,'log_pole_shift':fmt(delta),
                       'first_relative_error':fmt((approx1-delta)/delta),
                       'second_relative_error':fmt((approx2-delta)/delta),
                       'scaled_second_remainder':fmt((delta-approx2)/(h*h*eps**3))})
    result={'status':'PASS',
      'warning':'Decimal numerics are diagnostics, not certified interval enclosures.',
      'mpmath_dps':mp.mp.dps,'tail_depth':J,
      'tail_agreement_K_at_R':fmt(tail_agreement),
      'constants':{k:fmt(x) for k,x in constants.items()},
      'critical_checks':critical,'window_checks':windows,
      'height_checks':heights,'height_pole_checks':shifts}
    (OUT/'numerical_checks.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':run()
