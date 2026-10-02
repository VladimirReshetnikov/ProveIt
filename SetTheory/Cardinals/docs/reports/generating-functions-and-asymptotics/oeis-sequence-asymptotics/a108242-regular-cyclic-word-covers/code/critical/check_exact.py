"""Replay exact finite checks and critical-window numerical diagnostics.

No asymptotic formula is used to construct exact counts. Full integer counts are
saved; mpmath only converts the exact rational A/B and evaluates asymptotics.
"""
from pathlib import Path
from itertools import product
from fractions import Fraction
from math import factorial
from functools import lru_cache
import subprocess,json,argparse
import mpmath as mp
ROOT=Path(__file__).resolve().parent
mp.mp.dps=80

def necklaces(n):
    words={min(t,t[1:]+t[:1],t[2:]+t[:2]) for t in product(range(n),repeat=3)}
    return sorted(tuple(t.count(i) for i in range(n)) for t in words)

def direct_product(n,r,s):
    # Truncated multiplication of actual factors (1-w)^-1 or (1+w).
    zero=(0,)*n;dp={zero:1}
    for v in necklaces(n):
        out={}
        for ex,c in dp.items():
            maxcopies=min((r-e)//a for e,a in zip(ex,v) if a)
            if s==-1:maxcopies=min(maxcopies,1)
            for k in range(maxcopies+1):
                ee=tuple(e+k*a for e,a in zip(ex,v))
                out[ee]=out.get(ee,0)+c
        dp=out
    return dp.get((r,)*n,0)

def python_recurrence(n,r,s):
    # A compact independent implementation of the same exact derivative identity.
    @lru_cache(None)
    def rec(e):
        if not e:return 1
        a=e[0];rest=e[1:];total=0
        def term(ar,changes):
            rem=list(rest)
            for k,v in changes:rem[k]-=v
            if min(rem,default=0)<0:return 0
            if ar:rem.append(ar)
            return rec(tuple(sorted(v for v in rem if v)))
        for j in range(1,a+1):
            sg=s**(j-1)
            if 3*j<=a:total+=sg*3*term(a-3*j,[])
            if 2*j<=a:
                for k in range(len(rest)):total+=sg*2*term(a-2*j,[(k,j)])
            for k in range(len(rest)):total+=sg*term(a-j,[(k,2*j)])
            for k in range(len(rest)):
                for l in range(k+1,len(rest)):total+=sg*2*term(a-j,[(k,j),(l,j)])
        assert total%a==0
        return total//a
    return rec((r,)*n) if n*r%3==0 else 0

def cpp(n,r):
    return json.loads(subprocess.check_output([str(ROOT/'cyclic-exact'),str(n),str(r)],text=True))

def baseline(n,r):
    return Fraction(factorial(n*r),3**(n*r//3)*factorial(n*r//3)*factorial(r)**n)

def diagnostics(row):
    n,r=row['n'],row['r'];h=1/mp.sqrt(n);lam=r*h;B=baseline(n,r)
    result={'n':n,'r':r,'lambda':mp.nstr(lam,18),'states':row['states'],'seconds':row.get('seconds')}
    for s,name in [(1,'plus'),(-1,'minus')]:
        A=int(row[name]);rat=Fraction(A)/B
        Q=mp.mpf(rat.numerator)/rat.denominator/mp.exp(s*lam**2/6)
        if s==1:P=[1,lam/6,lam**2/72-mp.mpf(3)/2,mp.mpf(7)/(6*lam)-lam/4-71*lam**3/1296]
        else:P=[1,7*lam/6,49*lam**2/72-mp.mpf(5)/2,mp.mpf(3)/(2*lam)-35*lam/12+271*lam**3/1296]
        approximations=[sum(P[k]*h**k for k in range(K+1)) for K in range(4)]
        errors=[Q-a for a in approximations]
        result[name]={'A':str(A),'A_over_B':mp.nstr(Q*mp.exp(s*lam**2/6),35),'normalized_Q':mp.nstr(Q,35),'P0_through_P3_errors':[mp.nstr(e,25) for e in errors], 'h4_scaled_P3_error':mp.nstr(errors[3]/h**4,25)}
    return result

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--extended',action='store_true',help='also n=48,r=7; several million exact states');args=ap.parse_args()
    subprocess.run(['g++','-O3','-std=c++17',str(ROOT/'exact_counts.cpp'),'-lgmpxx','-lgmp','-o',str(ROOT/'cyclic-exact')],check=True)
    checks=[]
    for n in range(1,5):
        for r in range(1,7):
            if n*r%3:continue
            row=cpp(n,r)
            for s,name in [(1,'plus'),(-1,'minus')]:
                v=direct_product(n,r,s)
                assert v==python_recurrence(n,r,s)==int(row[name]),(n,r,s,v,row)
            checks.append({'n':n,'r':r,'plus':row['plus'],'minus':row['minus']})
    cases=[(9,3),(15,4),(24,5),(36,6),(12,3),(27,3),(48,3),(75,3),(108,3),(24,4),(48,4),(96,4),(15,5),(30,5),(60,5),(12,6),(24,6)]
    if args.extended:cases.append((48,7))
    results=[]
    for n,r in cases:
        row=diagnostics(cpp(n,r));results.append(row)
        print(n,r,'plus E3/h4',row['plus']['h4_scaled_P3_error'],'minus',row['minus']['h4_scaled_P3_error'],flush=True)
    if not args.extended and (ROOT/'extended-exact-count.json').exists():
        results.append(diagnostics(json.loads((ROOT/'extended-exact-count.json').read_text())))
    report={'extended_case_recomputed_in_this_run':args.extended, 'description':'Exact finite computations, not a proof of uniform asymptotic remainders. Q=(A/B)exp(-s lambda^2/6). Errors are Q minus the indicated asymptotic polynomial.', 'direct_necklace_product_crosschecks':checks,'numerical_cases':results}
    (ROOT/'exact-results.json').write_text(json.dumps(report,indent=2)+'\n')
    print('All direct-product, Python, and C++ crosschecks passed.')
