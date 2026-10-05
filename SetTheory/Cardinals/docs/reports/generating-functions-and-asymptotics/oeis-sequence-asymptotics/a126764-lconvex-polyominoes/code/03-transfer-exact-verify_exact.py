#!/usr/bin/env python3
"""Exact independent checks of OEIS A126764 and diagnostic asymptotic ratios.

Run: python verify_exact.py; python -O verify_exact.py
The b-file snapshot was retrieved 2026-10-02 from
https://oeis.org/A126764/b126764.txt (direct Python download returned 403).
The literal f-sum and f-recurrence are equations (3),(4) of
https://arxiv.org/html/2109.09928v3.
All tests use explicit exceptions, never optimization-disabled assertions.
"""
import argparse, hashlib, json, pathlib, sys, time
import mpmath as mp

HERE=pathlib.Path(__file__).resolve().parent

def divide_by_one_minus_qk(a,k):
    """Mutate truncated series a, multiplying by (1-q**k)**-1."""
    for i in range(k,len(a)):
        a[i]+=a[i-k]

def fast_coefficients(N):
    """b[-1]=b[0]=1; b[k]=(2*b[k-1]-b[k-2])/(1-q**k)**2.
    A=1+sum(k>=1) (q**k-q**(2*k))*b[k]. O(N**2)."""
    prevprev=[1]+[0]*N
    prev=prevprev.copy()
    a=prev.copy()
    for k in range(1,N+1):
        cur=[2*x-y for x,y in zip(prev,prevprev)]
        divide_by_one_minus_qk(cur,k)
        divide_by_one_minus_qk(cur,k)
        for j in range(N+1-k):
            a[j+k]+=cur[j]
        for j in range(N+1-2*k):
            a[j+2*k]-=cur[j]
        prevprev,prev=prev,cur
    return a

def literal_coefficients(N):
    """Independently use published f-recurrence and each literal summand.
    No b-transform. Every denominator factor is applied from scratch."""
    a=[1]+[0]*N
    fm2=None
    fm1=None
    for k in range(N):
        f=[0]*(N+1)
        if k==0:
            f[0]=1
        elif k==1:
            f[0]=1
            if N>=1: f[1]=2
            if N>=2: f[2]=-1
        else:
            for i in range(N+1):
                f[i]=2*fm1[i]-fm2[i]
                if i>=k: f[i]+=2*fm2[i-k]
                if i>=2*k: f[i]-=fm2[i-2*k]
        summand=f[:N-k]
        for j in range(1,k+1):
            divide_by_one_minus_qk(summand,j)
            divide_by_one_minus_qk(summand,j)
        divide_by_one_minus_qk(summand,k+1)
        for i,x in enumerate(summand):
            a[i+k+1]+=x
        fm2,fm1=fm1,f
    return a

def check_equal(a,b,name):
    if len(a)!=len(b):
        raise RuntimeError(f'{name}: lengths differ: {len(a)} != {len(b)}')
    for n,(x,y) in enumerate(zip(a,b)):
        if x!=y:
            raise RuntimeError(f'{name}: n={n}: {x} != {y}')

def nstr(x): return mp.nstr(x,60)

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--max-n',type=int,default=2000)
    p.add_argument('--literal-n',type=int,default=160)
    p.add_argument('--output',default='verification_results.json')
    args=p.parse_args()
    t=time.perf_counter(); exact=fast_coefficients(args.max_n)
    timing_fast=time.perf_counter()-t
    t=time.perf_counter(); literal=literal_coefficients(args.literal_n)
    timing_literal=time.perf_counter()-t
    check_equal(exact[:args.literal_n+1],literal,'published literal f-sum versus b-recurrence')
    rows={int(n):int(a) for n,a in (line.split() for line in (HERE/'b126764_web.txt').read_text().splitlines())}
    if set(rows)!=set(range(2001)):
        raise RuntimeError('OEIS snapshot must contain all 2001 entries n=0..2000')
    overlap=min(2000,args.max_n)
    check_equal(exact[:overlap+1],[rows[n] for n in range(overlap+1)],'OEIS b-file versus b-recurrence')
    mp.mp.dps=100
    C=13*mp.sqrt(2)/768
    beta=mp.pi*mp.sqrt(mp.mpf(13)/6)
    diagnostics=[]
    for n in [10,20,50,100,200,500,1000,1500,1936,2000,4000,8000]:
        if n>args.max_n: continue
        lead=C*mp.exp(beta*mp.sqrt(n))/mp.mpf(n)**mp.mpf('1.5')
        r=mp.mpf(exact[n])/lead
        diagnostics.append({'n':n,'a_n':str(exact[n]),'ratio_to_leading':nstr(r),
          'sqrt_n_times_ratio_minus_1':nstr(mp.sqrt(n)*(r-1)),
          'ratio_to_reciprocal_amplitude':nstr(r*C*C),
          'successive_ratio':nstr(mp.mpf(exact[n])/exact[n-1])})
    result={'sources':{'bfile':'https://oeis.org/A126764/b126764.txt',
      'paper':'https://arxiv.org/html/2109.09928v3','paper_equations':[3,4],
      'bfile_sha256':hashlib.sha256((HERE/'b126764_web.txt').read_bytes()).hexdigest()},
      'checks':{'oeis_all_2001_match':overlap==2000,'oeis_max_n_checked':overlap,
        'literal_f_sum_max_n_checked':args.literal_n,'python_optimization':sys.flags.optimize},
      'fast_seconds':timing_fast,'literal_seconds':timing_literal,
      'amplitude_C':nstr(C),'beta':nstr(beta),'diagnostics':diagnostics}
    (HERE/args.output).write_text(json.dumps(result,indent=2)+'\n')
    (HERE/f'exact_coefficients_{args.max_n}.json').write_text(json.dumps([str(x) for x in exact])+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()
