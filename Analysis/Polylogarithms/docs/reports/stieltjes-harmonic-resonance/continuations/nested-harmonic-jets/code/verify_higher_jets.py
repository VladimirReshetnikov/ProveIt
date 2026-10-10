#!/usr/bin/env python3
"""Coefficientwise diagnostics of the all-order resonance jet theorem."""
from __future__ import annotations
import json, math, time
from pathlib import Path
import mpmath as mp
mp.mp.dps=60
ROOT=Path(__file__).resolve().parents[1]

def li_nonpositive(r,t):
    if r==1:return t/(1-t)
    if r==2:return t/(1-t)**2
    if r==3:return t*(1+t)/(1-t)**3
    if r==4:return t*(1+4*t+t*t)/(1-t)**4
    raise ValueError('Verifier implements r <= 4')

def bell(L,R):
    Y=[mp.mpf(1)]
    for r in range(1,R+1):
        Y.append(mp.fsum(math.comb(r-1,j-1)*L[j]*Y[r-j] for j in range(1,r+1)))
    return Y

def main():
    start=time.time(); rows=[];R=4;N=32
    for m in range(1,7):
        b=[mp.mpf(1)]+[mp.mpf(0)]*R
        prefix=[mp.mpf(0)]*(R+1); lm=mp.log(m)
        for n in range(1,N+1):
            if n>1:
                k=n-1
                if k!=m:
                    for r in range(1,R+1):
                        prefix[r]+=(-1)**(r+1)*mp.log(k)**r*li_nonpositive(r,mp.mpf(m)/k)
            L=prefix.copy();L[1]-=mp.log(n)
            Y=bell(L,R)
            if n<=m:
                predicted=[(-1)**n*math.comb(m,n)*Y[r] for r in range(R+1)]
            else:
                base=mp.mpf((-1)**m*m)/((n-m)*math.comb(n,m))
                predicted=[mp.mpf(0)]+[base*mp.fsum((-1)**(j+1)*math.comb(r,j)*lm**j*Y[r-j] for j in range(1,r+1)) for r in range(1,R+1)]
            if n==1:ratio=[mp.mpf(-m)]+[mp.mpf(0)]*R
            else:
                ln=mp.log(n);lp=mp.log(n-1)
                ratio=[(mp.mpf(n-1)*(lp-ln)**r-m*(-ln)**r)/n for r in range(R+1)]
            b=[mp.fsum(math.comb(r,j)*ratio[j]*b[r-j] for j in range(r+1)) for r in range(R+1)]
            for r in range(R+1):
                absolute=abs(b[r]-predicted[r]);scaled=absolute/max(1,abs(b[r]),abs(predicted[r]))
                if scaled>mp.mpf('1e-45'):raise AssertionError((m,n,r,scaled))
                rows.append({'m':m,'n':n,'derivative':r,'absolute_residual':mp.nstr(absolute,16),'scaled_residual':mp.nstr(scaled,16)})
    report={'status':'PASS','checks':len(rows),'precision_decimal_digits':60,
            'max_scaled_residual':mp.nstr(max(mp.mpf(x['scaled_residual']) for x in rows),16),
            'seconds':time.time()-start,'scope':'Floating-point diagnostics, not interval certificates or a proof-assistant formalization.','rows':rows}
    (ROOT/'results'/'higher_jet_verification.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='rows'},indent=2))
if __name__=='__main__':main()
