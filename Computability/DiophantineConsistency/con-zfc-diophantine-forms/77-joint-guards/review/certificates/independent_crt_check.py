#!/usr/bin/env python3
"""Separate arithmetic regression for the index-free certificate and its ledger."""
from pathlib import Path
from math import comb,factorial,gcd,prod
import json,sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
from independent_local_check import need,padd,pmul
OUT=Path(__file__).resolve().parent

def power(p,n):
 r={(0,0):1}
 for _ in range(n):r=pmul(r,p)
 return r

def scale(p,n):return {m:n*c for m,c in p.items() if n*c}

def main():
 D={(1,0):1};i={(0,1):1};one={(0,0):1};one_minus_D=padd(one,D,-1);Di=pmul(D,i);modulus=padd(pmul(D,padd(i,one)),one,-1)
 algebra=0
 for d in range(21):
  for k in range(d+1):
   cleared=pmul(power(D,d-k),power(one_minus_D,k));uncleared=pmul(power(D,d),power(i,k))
   geometric={}
   for j in range(k):geometric=padd(geometric,pmul(power(one_minus_D,k-1-j),power(Di,j)))
   quotient=scale(pmul(power(D,d-k),geometric),-1)
   need(padd(cleared,uncleared,-1)==pmul(modulus,quotient),'exact cleared monomial identity');algebra+=1
 cases=0
 for H in range(1,14):
  D0=4*factorial(H)
  for n in range(H+1):
   S=D0**n*factorial(n);Q=S;M=D0*Q+1
   ms=[D0*j-1 for j in range(1,n+1)];B=prod(ms)
   need(B<M and (not n or B<S),'strict no-wrap bound')
   need(S*comb(Q+n,n)%M==B,'literal least-remainder identity')
   need(all(gcd(m,D0)==1 and m%4==3 for m in ms),'inert modulus support')
   need(all(gcd(ms[a],ms[b])==1 for a in range(n) for b in range(a)),'pairwise coprimality')
   need(all(gcd(factorial(H),m)==1 for m in ms),'no small prime divisors')
   cases+=1
 # Independent field diagnostics of index elimination and range selection.
 field=0
 for p in (7,11,19,23,31,43,47):
  need(p%4==3,'inert prime')
  for D0 in range(1,p):
   idx=(pow(D0,-1,p)-1)%p
   for A in range(p):
    U=2;R=D0*A+D0-1
    norm=(comb(A,U+1)**2+R*R)%p
    need((norm==0)==(A<=U and A==idx),'same-prime index-free range recovery');field+=1
 # Counterexample at split prime: two nonzero leaves can disappear in a norm.
 need((1**2+2**2)%5==0,'split-prime rejection')
 # Universal graph-slot ledger: U,A_j plus outputs of two factorial calls,
 # one power call, m+1 binomial calls, remainder and its quotient/slack,
 # and one final divisibility quotient.
 slots={'U_and_CRT_coordinates':'m+1','factorial_outputs':2,'power_output':1,'binomial_outputs':'m+1','remainder_B_quotient_slack':3,'norm_divisibility_quotient':1}
 for m in range(1,50):
  need((m+1)+2+1+(m+1)+3+1==2*m+9,'visible natural witness ledger')
 report={'status':'PASS','optimized_mode':not __debug__,'cleared_monomial_identities':algebra,'factorial_product_cases':cases,'field_range_residual_cases':field,'power_graph_calls':1,'factorial_graph_calls':2,'binomial_graph_calls':'m+1','visible_slots':slots,'conditional_total':'2m+9+2f+p+(m+1)b','scope':'Exact arithmetic/schema regressions and independently reconstructed conditional ledger. Universal theorem reviewed separately; no graph expansion or final consistency-polynomial count is supplied.'}
 target='CRT_CHECKS_OPTIMIZED.json' if not __debug__ else 'CRT_CHECKS.json';(OUT/target).write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
