#!/usr/bin/env python3
"""UNVERIFIED floating-point diagnostics, not certified amplitude bounds.

Directly computes the original A[n,k] row recurrence after dividing each
row by 12**n*n!.  This implementation does not use any Jacobi or Airy
profile recurrence.  Only the final comparison uses the proposed expansion.
"""
from pathlib import Path
import argparse
import json
import math
import time
import numpy as np
from scipy.special import ai_zeros

def exact_checks(nmax=80):
    old=[1];v=np.array([1.0]); maxerr=0.0
    initial=[]
    for n in range(1,nmax+1):
        row=[];acc=0
        for k in range(n+1):
            acc+=(2*n+k-1)*(old[k] if k<len(old) else 0)
            row.append(acc)
        old=row
        v=np.cumsum(np.pad(v,(0,1))*((2*n+np.arange(n+1)-1)/(12*n)))
        if n<=5: initial.append(row[-1])
        exact_scaled=row[-1]/(12**n*math.factorial(n))
        maxerr=max(maxerr,abs(v[-1]/exact_scaled-1))
    assert initial==[1,7,106,2575,87595],initial
    assert maxerr<1e-13,maxerr
    return {'nmax':nmax,'initial_diagonal':initial,'max_relative_error_vs_exact_integer':maxerr}

def run(nmax, extended=False):
    dtype=np.longdouble if extended else np.float64
    z=dtype(ai_zeros(1)[0][0]);B=z*dtype(3)**(dtype(1)/3)
    logs=[B*B/18,dtype(0),-dtype(1)/9,-B*B/162]
    v=np.zeros(nmax+1,dtype=dtype);v[0]=1
    index=np.arange(nmax+1,dtype=dtype)
    checkpoints={10,30,100,300,1000,3000,10000,20000,30000,50000,nmax}
    rows=[];start=time.perf_counter()
    for n in range(1,nmax+1):
        # old[n]=0.  The boundary column and every interior entry obey the
        # same weighted cumulative sum after row normalization.
        v[n]=0
        v[:n+1]*=(index[:n+1]+(2*n-1))/(12*n)
        np.cumsum(v[:n+1],out=v[:n+1])
        if n in checkpoints:
            t=dtype(n)**(-dtype(1)/3)
            rawlog=np.log(v[n])-B/t+(dtype(2)/3)*np.log(dtype(n))
            corrected=[];shift=dtype(0)
            for k,L in enumerate(logs,1):
                shift+=L*t**k
                corrected.append(float(np.exp(rawlog-shift)))
            row={'n':n,'raw_amplitude':float(np.exp(rawlog)),
                 'corrected_after_log_order_1':corrected[0],
                 'corrected_after_log_order_2':corrected[1],
                 'corrected_after_log_order_3':corrected[2],
                 'corrected_after_log_order_4':corrected[3]}
            rows.append(row);print(('longdouble' if extended else 'float64'),row,flush=True)
    elapsed=time.perf_counter()-start
    return {'warning':'UNCERTIFIED floating-point diagnostics. These are finite-n amplitude approximations, not rigorous error bounds or a certified value of gamma.',
            'dtype':str(np.dtype(dtype)),'nmax':nmax,'elapsed_seconds':elapsed,
            'z_double_precision':float(z),'B':float(B),
            'log_coefficients':[float(a) for a in logs],'rows':rows}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--nmax',type=int,default=50000)
    ap.add_argument('--extended-check',type=int,default=10000);args=ap.parse_args()
    data={'exact_small_n_check':exact_checks(),'primary':run(args.nmax)}
    if args.extended_check:
        data['extended_precision_check']=run(args.extended_check,True)
        common={r['n']:r for r in data['primary']['rows']}
        comparisons=[]
        for row in data['extended_precision_check']['rows']:
            if row['n'] in common:
                a=common[row['n']]['corrected_after_log_order_4'];b=row['corrected_after_log_order_4']
                comparisons.append({'n':row['n'],'float64_vs_longdouble_relative_difference':a/b-1})
        data['roundoff_comparisons']=comparisons
    Path(__file__).with_name('forward-numerical.json').write_text(json.dumps(data,indent=2)+'\n')

if __name__=='__main__':main()
