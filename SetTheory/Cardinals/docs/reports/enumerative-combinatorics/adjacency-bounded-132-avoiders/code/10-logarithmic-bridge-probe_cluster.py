#!/usr/bin/env python3
"""Floating-point root and cluster diagnostics; not a proof or error certificate."""
from pathlib import Path
import json, math, platform
import numpy as np
import scipy
from scipy.optimize import brentq


def block_ratio(k,d):
    if k<=d+1:
        return 1.0
    product=1.0
    total=0.0
    for j in range(1,d+1):
        total+=j*product
        product*=(k-1-j)/(2*k-3-j)
    return k/(4*k-6)*total


def calculate(m):
    d=(m-1).bit_length();M=m-d
    b=np.empty(m)
    b[0]=0.25
    for k in range(1,m):
        b[k]=b[k-1]*(1-1.5/(k+1))
    j=np.arange(1,m+1,dtype=float)
    t=brentq(lambda t:np.dot(b,np.exp(t*j/m))-1,0,2*math.log(m)+10,
             xtol=1e-13)
    r=math.exp(t/m)/4
    ratio=np.array([block_ratio(k,d) for k in range(1,M+1)])
    low=b[:M]*ratio;k=j[:M]
    tau=brentq(lambda t:np.dot(low,np.exp(t*k/M))-1,0,2*math.log(m)+10,
               xtol=1e-13)
    lam=tau/M;w=1/lam;s=math.exp(lam)/4
    p=low*np.exp(lam*k)
    root_residual=float(p.sum()-1)
    p=p/p.sum()
    small=k<=M//2
    a=float(p[small].sum());bmass=float(p[~small].sum())
    A1=float(np.dot(p[small],k[small]));A2=float(np.dot(p[small],k[small]**2))
    B1=float(np.dot(p[~small],k[~small]));B2=float(np.dot(p[~small],k[~small]**2))
    mean=B1/bmass+A1/(1-a)
    variance=B2/bmass-(B1/bmass)**2+A2/(1-a)+(A1/(1-a))**2
    return dict(m=m,d=d,M=M,r_m=r,s_m=s,t_m=t,tau=tau,w=w,
                lower_root_residual=root_residual,
                root_corridor_scaled=(s-r)*m*m/math.log(m)**2,
                small_mass=a,big_mass=bmass,cluster_mean=mean,
                normalized_mean_deficit=(M-mean)/w,
                cluster_sd_over_w=math.sqrt(variance)/w,
                centered_root_remainder=t-0.5*math.log(m)-math.log(math.log(m)),
                target_centered_root_remainder=0.5*math.log(math.pi))


def main():
    rows=[calculate(m) for m in (32,64,128,256,512,1024,2048,4096)]
    assert all(abs(row['lower_root_residual'])<1e-10 for row in rows)
    assert all(row['s_m']>=row['r_m'] for row in rows)
    result=dict(status='finite sanity checks passed',
                scope='Ordinary floating-point diagnostics; no convergence rate or certified enclosure.',
                environment=dict(python=platform.python_version(),numpy=np.__version__,scipy=scipy.__version__),
                rows=rows)
    Path(__file__).with_name('cluster_diagnostics.json').write_text(json.dumps(result,indent=2)+'\n')
    for row in rows:
        print(row['m'],row['small_mass'],row['normalized_mean_deficit'],row['cluster_sd_over_w'])


if __name__=='__main__':
    main()
