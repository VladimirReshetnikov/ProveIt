#!/usr/bin/env python3
"""Optional floating-point checks; not an asymptotic proof or enclosure."""
from pathlib import Path
import json,math,platform
import numpy as np
import scipy
from scipy.optimize import brentq
import mpmath as mp


def law(m):
    b=np.empty(m);b[0]=.25
    for k in range(1,m):b[k]=b[k-1]*(1-1.5/(k+1))
    k=np.arange(1,m+1,dtype=float)
    t=brentq(lambda x:np.dot(b,np.exp(x*k/m))-1,0,2*math.log(m)+10,xtol=1e-13)
    r=math.exp(t/m)/4
    p=b*np.exp(t*k/m);residual=float(p.sum()-1);p/=p.sum()
    small=k<=m//2;bmass=float(p[~small].sum())
    A1=float(np.dot(k[small],p[small]));B1=float(np.dot(k[~small],p[~small]))
    P2=float(np.dot(k*k,p));nu=A1+B1;mu=nu/bmass
    variance=P2/bmass+(A1*A1-B1*B1)/(bmass*bmass)
    return p,r,nu,mu,math.sqrt(variance),residual


def theta(H,u):
    return 1+2*sum(math.exp(-2*math.pi**2*H*H*j*j)*math.cos(2*math.pi*j*u)
                   for j in range(1,1+max(10,math.ceil(8/H))))


def coefficients(p,n):
    m=len(p);renew=np.zeros(n+1);square=np.zeros(n+1)
    renew[0]=square[0]=1
    for v in range(1,n+1):
        q=min(v,m)
        renew[v]=np.dot(p[:q],renew[v-q:v][::-1])
        square[v]=renew[v]+np.dot(p[:q],square[v-q:v][::-1])
    return square


def main():
    mp.mp.dps=75;dual=[]
    for h in ('0.125','0.25','0.5','1','2'):
        for u in ('0','0.125','0.5','0.75'):
            H=mp.mpf(h);x=mp.mpf(u)
            limit=int(mp.ceil(22*H+abs(x)))+5
            direct=mp.fsum(mp.exp(-(j-x)**2/(2*H*H))/(H*mp.sqrt(2*mp.pi))
                          for j in range(-limit,limit+1))
            lim2=int(mp.ceil(6/H))+5
            fourier=1+2*mp.fsum(mp.exp(-2*mp.pi**2*H*H*j*j)*mp.cos(2*mp.pi*j*x)
                                for j in range(1,lim2+1))
            error=abs(direct-fourier)
            assert error<mp.mpf('1e-65')
            dual.append(dict(H=h,u=u,error=mp.nstr(error,12)))
    rows=[];stability=[]
    for m in (64,128,256,512,1024,2048):
        p,r,nu,mu,sigma,res=law(m)
        targets=[max(1,round(mu*(ell+u))) for ell in (4,8,16) for u in (0,.5)]
        coeff=coefficients(p,max(targets)-1)
        for n in targets:
            L=n/mu;H=sigma*math.sqrt(L)/mu
            normalized=float(coeff[n-1])*nu*nu/n
            mod=theta(H,L)
            rows.append(dict(m=m,n=n,L=L,H=H,normalized_envelope=normalized,
                             theta=mod,ratio_to_theta=normalized/mod,root_residual=res))
        d=2*math.ceil(3*math.log2(m));M=m-d
        if M>=2:
            p2,r2,nu2,mu2,sigma2,res2=law(M)
            extended=np.pad(p2,(0,d));distance=float(np.abs(extended-p).sum())
            tail=float(p[M:].sum())
            assert abs(distance-2*tail)<1e-11
            stability.append(dict(m=m,M=M,d=d,l1=distance,twice_removed_mass=2*tail,
                                 mean_shift=mu2-mu,variance_shift=sigma2*sigma2-sigma*sigma))
    data=dict(status='finite diagnostics passed',
              scope='Floating-point and high-precision diagnostics only; no certified asymptotic error or convergence cutoff.',
              environment=dict(python=platform.python_version(),numpy=np.__version__,scipy=scipy.__version__,mpmath=mp.__version__),
              gaussian_fourier_checks=dual,parameter_stability=stability,envelope_rows=rows)
    Path(__file__).with_name('theta_diagnostics.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(dict(status=data['status'],gaussian_fourier_checks=len(dual),
                          parameter_stability_checks=len(stability),envelope_rows=len(rows))))

if __name__=='__main__':main()
