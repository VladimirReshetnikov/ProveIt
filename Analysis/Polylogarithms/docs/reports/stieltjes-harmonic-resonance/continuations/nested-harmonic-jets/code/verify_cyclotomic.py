#!/usr/bin/env python3
"""Higher-genus cyclotomic product diagnostics (not interval certification)."""
from __future__ import annotations
import json,time
from pathlib import Path
import mpmath as mp
from verify_numeric import product_G
mp.mp.dps=60
ROOT=Path(__file__).resolve().parents[1]

def higher_G(M,s,z,a,N=16,K=100):
    if mp.re(s)<=mp.mpf(1)/(M+1):raise ValueError('Outside genus convergence half-plane')
    lin=mp.mpf(0)
    for k in range(1,M+1):
        t=k*s
        h=-mp.digamma(a) if abs(t-1)<mp.mpf('1e-55') else mp.zeta(t,a)-1/(t-1)
        lin+=(-1)**(k-1)*z**k*h/k
    out=mp.exp(lin)
    for n in range(N):
        t=z/mp.power(n+a,s)
        out*=(1+t)*mp.exp(mp.fsum((-1)**k*t**k/k for k in range(1,M+1)))
    tail=mp.fsum((-1)**(k-1)*z**k*mp.zeta(k*s,a+N)/k for k in range(M+1,K+1))
    return out*mp.exp(tail)

def main():
    start=time.time();rows=[]
    for m in range(2,6):
        omega=mp.exp(2j*mp.pi/m)
        for a in [mp.mpf(1),mp.mpf('1.3')]:
            for offset in [mp.mpc(0),mp.mpc('0.02','0.03')]:
                s=mp.mpf(1)/m+offset;z=mp.mpc('.17','.08');u=(-1)**(m+1)*z**m
                lhs=mp.fprod(higher_G(m,s,omega**j*z,a) for j in range(m))
                rhs=mp.gamma(a)*mp.rgamma(a+u) if offset==0 else product_G(m*s,u,a)
                err=abs(lhs-rhs)/max(1,abs(lhs),abs(rhs))
                if err>mp.mpf('1e-44'):raise AssertionError((m,a,s,err))
                rows.append({'m':m,'a':str(a),'s':str(s),'scaled_residual':mp.nstr(err,16)})
    report={'status':'PASS','checks':len(rows),'precision_decimal_digits':60,
            'max_scaled_residual':mp.nstr(max(mp.mpf(x['scaled_residual']) for x in rows),16),
            'seconds':time.time()-start,'scope':'Arbitrary-precision floating-point diagnostics, not interval certificates.','rows':rows}
    (ROOT/'results'/'cyclotomic_verification.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='rows'},indent=2))
if __name__=='__main__':main()
