#!/usr/bin/env python3
"""Finite adversarial regressions for the signed lemmas; not their proofs."""
from pathlib import Path
import argparse, json, math

def choose(n,k):
    if n>=0:return math.comb(n,k) if k<=n else 0
    return (-1)**k*math.comb(-n+k-1,k)

def pell(A,k):
    X,Y=1,0
    for _ in range(abs(k)):X,Y=A*X+(A*A-1)*Y,X+A*Y
    return X, Y if k>=0 else -Y

def main():
    counts={'signed_coefficient_bounds':0,'signed_range_cases':0,'negative_series_truncations':0,'common_root_evaluations':0,'cofinal_ternary_representations':0}
    for n in range(-100,101):
        for k in range(31):
            c=choose(n,k)
            if abs(c)>max(1,abs(n))**k:raise ValueError(('coefficient',n,k,c))
            counts['signed_coefficient_bounds']+=1
            if k:
                for p in (2,3,5,7):
                    for e in range(1,5):
                        mod=p**e
                        if c%mod==0 and n%mod>=k:raise ValueError(('range',n,k,p,e))
                        counts['signed_range_cases']+=1
    for q in (3,5,9,15):
        for n in range(-20,21):
            for k in range(11):
                mod=q**(k+1); series=sum(choose(n,j)*q**j for j in range(k+1))
                if (pow(q+1,n,mod)-series)%mod:raise ValueError(('truncation',q,n,k))
                counts['negative_series_truncations']+=1
        for N in range(1,q+1,2):
            if q%N:continue
            for x in range(1,5):
                omega=N*q**x;n=q+1
                A=((n*n+1)*pow(2*n,-1,omega))%omega+2*omega
                if (2*A*n-n*n-1)%omega:raise ValueError(('root',q,N,x))
                for e in range(-12,13):
                    X,Y=pell(A,e);mu=X+(n-A)*Y
                    if (mu-pow(n,e,omega))%omega:raise ValueError(('Pell substitution',q,N,x,e))
                    counts['common_root_evaluations']+=1
    # Exhaustive small G values exercise the nonnegative cofinal slack.
    limit=1000;values=set()
    for u in range(math.isqrt(limit)+1):
        for v in range(math.isqrt(limit-u*u)+1):
            for w in range(math.isqrt(limit-u*u-v*v)+1):
                z=u*u+v*v+w*(w+1)
                if z<=limit:values.add(z)
    if values!=set(range(limit+1)):raise ValueError(('ternary missing',sorted(set(range(limit+1))-values)))
    counts['cofinal_ternary_representations']=limit+1
    return {'status':'passed','scope':'Finite regressions only. Unbounded proofs are in MODULAR_PROOF.md.', 'checks':counts}

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path);a=ap.parse_args()
    r=main()
    if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
    print(json.dumps(r,indent=2))
