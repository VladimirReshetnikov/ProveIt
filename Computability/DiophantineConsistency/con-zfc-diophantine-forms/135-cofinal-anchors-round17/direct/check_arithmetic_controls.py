#!/usr/bin/env python3
"""Independent finite regression controls; not a proof of the unbounded theorem."""
from math import gcd
from pathlib import Path
import argparse,json

def need(p,s):
 if not p:raise ValueError(s)
def pell(a,k):
 x,y=1,0
 for _ in range(abs(k)):x,y=a*x+(a*a-1)*y,x+a*y
 return x,y if k>=0 else -y

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path);args=ap.parse_args();counts={'signed_recurrence_residues':0,'negative_power_exclusion':0,'odd_auxiliary':0,'zero_upper_binomial':0,'strict_majorant_dyadic':0}
 for W in range(4,10):
  aa=W**W+1
  for a in (-aa,aa):
   for k in range(-W+1,W):
    x,y=pell(a,k)
    need((x-1)%(a-1)==0 and (y-k)%(a-1)==0,'canonical signed residue')
    counts['signed_recurrence_residues']+=1
    for n in range(2,W):
     T=2*a*n-n*n-1;R=x+(n-a)*y
     need(gcd(n,T)==1,'noninvertible positive base')
     if k<0:need((R*n**(-k)-1)%T==0,'inverse recurrence residue')
     else:need((R-n**k)%T==0,'direct recurrence residue')
     for m in range(-W+1,W):
      if (R-m)%T==0:need(k>=0 and m==n**k,'spurious small signed power')
      counts['negative_power_exclusion']+=1
 for a in range(2,6):
  for h in (2,4):
   U,C=pell(a,h);H,J=pell(a,h*C)
   need(C%2==0 and U%2==1,'even-index parity')
   need(J%(C*C)==0 and (J//(C*C))%2==1,'odd auxiliary quotient')
   need(H%2==1 and gcd(H,8*J)==1,'odd auxiliary CRT coprimality')
   counts['odd_auxiliary']+=1
 from math import comb
 for k in range(1,80):
  need(comb(0,k)==0,'zero upper binomial')
  for j in range(k+1):need(comb(0,j)<=max(1,0)**k,'zero upper coefficient bound')
  counts['zero_upper_binomial']+=1
 E=2**23
 for n in range(33,257):
  need(E*(n+1)<=2**(n-1),'strict dyadic majorant')
  counts['strict_majorant_dyadic']+=1
 out={'status':'passed','counts':counts,'total':sum(counts.values()),'scope':'Finite arithmetic regression only. Unbounded proofs are supplied separately and no consistency claim is tested.'}
 if args.output:args.output.write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps(out,indent=2))
if __name__=='__main__':main()
