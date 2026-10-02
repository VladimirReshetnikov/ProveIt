#!/usr/bin/env python3
"""Exact quadratic binomial-convolution recurrence; independent insertion check."""
import argparse,json,math,time,sys
from pathlib import Path

def cumulant_recurrence(N):
    ell=[0]; a=[1]
    for n in range(N):
        row=1; tot=2*ell[n]+1+2*(n==0)-(n==1)
        for k in range(n):
            tot+=row*ell[k+1]
            row=row*(n-k)//(k+1)
        q,r=divmod(tot,3)
        assert not r
        ell.append(q)
        row=1; tot=0
        for k in range(n+1):
            tot+=row*ell[k+1]*a[n-k]
            row=row*(n-k)//(k+1)
        a.append(tot)
    return ell,a

def insertion_recurrence(N):
    """BCK Proposition 11 five insertion rules, no EGF used."""
    if not N:return [1]
    states={(2,1):1};a=[1,1]
    for n in range(1,N):
        new={}
        def add(k,l,v):new[k,l]=new.get((k,l),0)+v
        for (k,l),v in states.items():
            if l<=k:
                for j in range(1,l+1):add(k+1,j,v)
                for j in range(l+1,k+1):add(j,j,v)
                for j in range(k+1,n+2):add(k,j,v)
            else:
                for j in range(1,k+1):add(k+1,j,v)
                for j in range(k+1,l+1):add(k,j,v)
        states=new;a.append(sum(states.values()))
    return a

def brute_avoid(N):
    from itertools import permutations
    out=[]
    for n in range(N+1):
        count=0
        for p in permutations(range(n)):
            ok=True
            for i in range(n-1):
                if p[i]<p[i+1] and any(p[i+1]<p[j]<p[j+1] for j in range(i+2,n-1)):
                    ok=False;break
            count+=ok
        out.append(count)
    return out

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--n',type=int,default=1000);ap.add_argument('--check-n',type=int,default=65);ap.add_argument('--brute-n',type=int,default=8);args=ap.parse_args()
    assert args.n>=0
    if hasattr(sys,"set_int_max_str_digits"):sys.set_int_max_str_digits(0)
    args.check_n=min(args.check_n,args.n);args.brute_n=min(args.brute_n,args.n)
    start=time.monotonic();ell,a=cumulant_recurrence(args.n)
    p=insertion_recurrence(args.check_n);b=brute_avoid(args.brute_n)
    assert p==a[:len(p)];assert b==a[:len(b)]
    oeis=[1,1,2,6,23,107,585,3669,25932,203768,1761109,16595757,169287873,1857903529,21823488238,273130320026,3627845694283,50962676849199,754814462534449,11754778469338581,191998054346198680]
    assert a[:len(oeis)]==oeis[:len(a)]
    path=Path(__file__).with_name('exact_values.json')
    path.write_text(json.dumps({'max_n':args.n,'ell':[str(x) for x in ell],'a':[str(x) for x in a],'checks':{'insertion_n':args.check_n,'bruteforce_n':args.brute_n,'oeis_terms':min(len(oeis),len(a))}},indent=2)+'\n')
    print('All exact checks passed; n=',args.n,'time=',time.monotonic()-start,flush=True)
if __name__=='__main__':main()
