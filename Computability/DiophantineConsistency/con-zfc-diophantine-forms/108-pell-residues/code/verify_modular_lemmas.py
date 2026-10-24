#!/usr/bin/env python3
"""Independent finite fixtures for the unbounded modular lemmas.

These fixtures detect algebraic/transcription mistakes; they are not a proof of
source calibration or of the unbounded theorems in MODULAR_BINOMIAL_PROOF.md.
Only Python's standard library is used and assertions are not relied on.
"""
from math import gcd,comb
from pathlib import Path
import json,argparse

def require(ok,message):
    if not ok:raise ValueError(message)

def pell(a,n):
    x,y=1,0
    for _ in range(n):x,y=a*x+(a*a-1)*y,x+a*y
    return x,y

def cofinal_parameter(q,H,lower):
    b=q+1;M=q**(H+1);d=gcd(2*b,M)
    require((b*b+1)%d==0,'linear congruence obstruction')
    period=M//d
    residue=((b*b+1)//d*pow((2*b)//d,-1,period))%period if period>1 else 0
    a=residue+max(0,(lower-residue+period-1)//period)*period
    require(a>=lower and (2*a*b-b*b-1)%M==0,'cofinal root')
    return a,M

def verify():
    root_tests=residue_tests=exact_tests=div_tests=negative_tests=0
    for q in range(2,25):
      for H in range(1,7):
        a,M=cofinal_parameter(q,H,q+100)
        root_tests+=1
        for n in range(1,19):
          x,y=pell(a,n);R=x+(q+1-a)*y
          require(x*x-(a*a-1)*y*y==1,'norm identity')
          require(R>0,'positive Pell image')
          require((R-pow(q+1,n))%M==0,'modular power identity')
          residue_tests+=1
          for k in range(1,H+1):
            if any(comb(n,j)>=q for j in range(min(k,n)+1)):continue
            c=comb(n,k) if k<=n else 0
            d=q**k;res=R%(q*d)
            require(res//d==c,'exact low digit')
            r=res%d;h=(R-res)//(q*d)
            require(0<=r<d and 0<=c<q and h>=0,'exact natural witnesses')
            require(x+(q+1)*y==a*y+r+d*c+q*d*h,'exact row')
            exact_tests+=1
            for B in range(1,q+1):
              if q%B:continue
              residue=R%(B*d)
              require((residue<d)==(c%B==0),'binomial divisibility equivalence')
              if c%B==0:
                h=(R-residue)//(B*d)
                require(h>=0 and x+(q+1)*y==a*y+residue+B*d*h,'range row')
              div_tests+=1
    # A corrupted root congruence must invalidate some modular power identity.
    a,M=cofinal_parameter(5,3,100)
    bad=a+1;x,y=pell(bad,2)
    require((x+(6-bad)*y-36)%M!=0,'root mutation not detected');negative_tests+=1
    # Lower coefficient bounds are necessary, not a cosmetic hypothesis.
    q,n,k=2,3,2
    require((q+1)**n//q**k%q!=comb(n,k),'carry mutation not detected');negative_tests+=1
    # Dropping the one-digit upper bound admits a wrong digit, compensated below.
    q,n,k=7,2,1
    value=(q+1)**n;d=q**k;c=comb(n,k);r=value%d
    bad_c=c+q
    require(value==r+d*bad_c+q*d*(value//(q*d)-1),'digit-bound negative control');negative_tests+=1
    return {'status':'PASS','root_congruences':root_tests,'pell_residue_identities':residue_tests,
            'exact_low_digit_cases':exact_tests,'binomial_divisibility_cases':div_tests,
            'negative_controls':negative_tests,'scope':'finite exact arithmetic fixtures, not unbounded proof'}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path);a=p.parse_args()
    r=verify();s=json.dumps(r,indent=2,sort_keys=True)+'\n'
    if a.output:a.output.write_text(s)
    print(s,end='')
