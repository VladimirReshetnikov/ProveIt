#!/usr/bin/env python3
"""Non-certified high precision experiment. Only the comparison uses zeta zeros.
Requires mpmath. Recompute with --dps 140 --samples 512 for stability.
"""
import argparse, csv, sys
import mpmath as mp
from pathlib import Path

def moments(kmax, M):
    # Scaled variable y=200/(1/4+gamma^2). Log E(200z) is analytic
    # near 0. Discrete Cauchy coefficients on radius 1/5.
    radius=mp.mpf(1)/5
    sums=[mp.mpc(0) for _ in range(kmax+1)]
    for l in range(M//2+1):
        theta=2*mp.pi*l/M
        u=mp.exp(1j*theta)
        z=radius*u
        s=mp.mpf('0.5')+mp.sqrt(mp.mpf('0.25')-200*z)
        E=s*(s-1)*mp.power(mp.pi,-s/2)*mp.gamma(s/2)*mp.zeta(s)
        f=mp.log(E)
        mult=1 if l in (0,M//2) else 2
        t=mp.mpc(1)
        for k in range(1,kmax+1):
            t*=mp.conj(u)
            sums[k]+=mult*mp.re(f*t)
    return [None]+[-k*mp.re(sums[k])/M/radius**k for k in range(1,kmax+1)]

def pencil(m, nmax):
    def inner(a,b,shift=0):
        return mp.fsum(a[i]*b[j]*m[i+j+1+shift] for i in range(len(a)) for j in range(len(b)))
    polys=[[mp.mpf(1)]]; hs=[m[1]]; bs=[]; aa=[]; ts=[]
    for n in range(nmax+1):
        p=polys[n]
        b=inner(p,p,1)/hs[n]; bs.append(b); ts.append(inner(p,p,2)/hs[n])
        if n==nmax: break
        q=[mp.mpf(0)]+p[:]
        for k in range(n+1): q[k]-=b*p[k]
        if n:
            for k in range(n): q[k]-=aa[n-1]*polys[n-1][k]
        h=inner(q,q); assert h>0, (n,h)
        polys.append(q); hs.append(h); aa.append(h/hs[n])
    return hs,bs,aa,ts

def main():
    p=argparse.ArgumentParser();p.add_argument('--dps',type=int,default=110);p.add_argument('--samples',type=int,default=320);p.add_argument('--nmax',type=int,default=14);p.add_argument('--output',default='experiment.csv');args=p.parse_args()
    assert args.samples%2==0
    mp.mp.dps=args.dps
    m=moments(2*args.nmax+3,args.samples)
    hs,bs,aa,ts=pencil(m,args.nmax)
    # Reference only, never used in the pencils or estimator.
    refs=[200/(mp.mpf('0.25')+mp.im(mp.zetazero(j))**2) for j in range(1,4)]
    rows=[]; previous={}
    for n in range(3,args.nmax+1):
        J=mp.matrix(n)
        for i in range(n):
            J[i,i]=bs[i]
            if i+1<n: J[i,i+1]=J[i+1,i]=mp.sqrt(aa[i])
        vals,U=mp.eigsy(J); cur=[]
        for j,x in enumerate(refs,1):
            i=n-j; r=vals[i]; v=aa[n-1]*U[n-1,i]**2; d=x-r
            assert d>0 and v>0
            est=v/r; refined=est*(1+bs[n]/r)
            ratio=d/est
            step=mp.nan if j not in previous else d/previous[j][0]*refs[j-1]**2/aa[n-1]
            cur.append(d)
            rows.append(dict(N=n,rank=j,delta=mp.nstr(d,18),delta_over_est=mp.nstr(ratio,15),relative_error_first=mp.nstr(abs(d-est)/d,12),relative_error_refined=mp.nstr(abs(d-refined)/d,12),step_ratio=mp.nstr(step,12),next_term_ratio=mp.nstr((d-refined)/(est*ts[n]/r**2),12),residual_mean=mp.nstr(bs[n],12)))
            previous[j]=(d,r)
        # Relative constant for ranks 2 and 1, converges to fixed positive limit.
        for k in range(3): rows[-3+k]['normalized_ratio_to_rank1']=mp.nstr(cur[k]/cur[0]*(refs[k]/refs[0])**(2*n),15)
    with open(args.output,'w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
    print('mpmath',mp.__version__,'dps',args.dps,'samples',args.samples,'nmax',args.nmax)
    print('Scaled p1:',mp.nstr(m[1],35))
    print('N   j  delta/(v/r)    corrected rel error    step ratio    normalized rank ratio')
    for row in rows:
        if row['N'] in (4,8,12,args.nmax): print(row['N'],row['rank'],row['delta_over_est'],row['relative_error_refined'],row['step_ratio'],row['normalized_ratio_to_rank1'])
if __name__=='__main__': main()
