#!/usr/bin/env python3
"""Exact recurrence integers and non-certified high-precision diagnostics.

The decimal C_T below is historical, not an interval-certified constant.
Requires Python 3 and mpmath. No network, external inputs, or fitted coefficients.
"""
import argparse, json, math, time
from pathlib import Path
import mpmath as mp

def takeuchi(N):
    T=[0]; cat=1; forcing=0
    for n in range(1,N+1):
        cat=cat*2*(2*n-1)//(n+1); forcing+=cat
        value=forcing; binomial=1
        for k in range(n):
            c=binomial*(n-k)//n
            value+=c*T[n-k-1]
            binomial=binomial*(n+k)//(k+1)
        T.append(value)
    return T

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--max-n',type=int,default=1500)
    ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    if args.max_n<10: ap.error('--max-n must be at least 10')
    mp.mp.dps=70; start=time.perf_counter(); T=takeuchi(args.max_n)
    assert T[:10]==[0,1,4,14,53,223,1034,5221,28437,165859]
    CT=mp.mpf('2.239433104005260731754785')
    rows=[]
    for n in sorted(set(x for x in [50,100,200,500,1000,1500,args.max_n] if x<=args.max_n)):
        w=mp.lambertw(n)
        F=mp.exp(w)*(w*w-w+1); g=w*w/2-mp.log(1+w)/2
        p1=-w*w*(26*w*w+67*w+46)/(24*(1+w)**3)
        p2=-w*w*(12*w**6+100*w**5+310*w**4+457*w**3+310*w*w+36*w-54)/(48*(1+w)**6)
        p3=w**3*(240*w**10-592*w**9-29028*w**8-188952*w**7-607146*w**6-1152408*w**5-1338579*w**4-884496*w**3-205104*w*w+133296*w+103040)/(17280*(1+w)**9)
        e0=mp.log(T[n])-(F+g+mp.log(CT)-1)
        e1=e0-p1/n; e2=e1-p2/n**2; e3=e2-p3/n**3
        row={'n':n,'w':str(w),'error_after_first':str(e1),'error_after_second':str(e2),'error_after_third':str(e3)}
        rows.append(row)
        print('n=%d: first=%s second=%s third=%s'%(n,*[mp.nstr(e,12) for e in [e1,e2,e3]]))
    out={'status':'non-certified diagnostic; decimal C_T is not enclosed','C_T_decimal':str(CT),'precision_digits':mp.mp.dps,'seconds':time.perf_counter()-start,'rows':rows}
    if args.output: args.output.write_text(json.dumps(out,indent=2)+'\n')
    print('Initial values: PASS; no numerical enclosure or remainder certificate is claimed.')
if __name__=='__main__': main()
