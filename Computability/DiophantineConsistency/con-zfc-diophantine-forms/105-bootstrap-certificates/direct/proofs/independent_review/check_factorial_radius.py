#!/usr/bin/env python3
"""Exact supplementary regression checks for the proved factorial identity.
These finite checks do not replace factorial_square_radius.md.
"""
from fractions import Fraction
from math import comb,factorial
from pathlib import Path
import json,sys

def need(ok,label):
 if not ok:raise ValueError(label)
def ceiling(n,d):return (n+d-1)//d

def check():
 points=0
 for n in range(13):
  K=factorial(n)
  trials=set(range(201))|{max(0,K-2),max(0,K-1),K,K+1,K+2}
  for F in sorted(trials):
   R=F*F;N=(R+1)**n;C=comb(R+n,n)
   need((ceiling(N,C)==F)==(F==K),'square-radius fixed point')
   # The two nonnegative residual witnesses exactly encode the ceiling.
   remainder=N+C-C*F-1;slack=C-remainder-1
   need((remainder>=0 and slack>=0)==(ceiling(N,C)==F),'literal ceiling rows')
   points+=1
 table=[]
 for F in range(1,7):
  R=F*F;f=Fraction((R+1)**3,comb(R+3,3))
  table.append({'candidate':F,'numerator':f.numerator,'denominator':f.denominator,'ceiling':ceiling(f.numerator,f.denominator)})
 need([r['ceiling'] for r in table]==[2,4,5,6,6,6],'all exceptional n3 possibilities')
 shared=0
 for H in range(13):
  R=factorial(H)**2
  for n in range(H+1):
   N=(R+1)**n;C=comb(R+n,n)
   need(ceiling(N,C)==factorial(n),'shared square radius')
   shared+=1
 return {'status':'PASS','python_optimization':sys.flags.optimize,'fixed_point_cases':points,
         'shared_radius_cases':shared,'n3_complete_case_table':table,
         'scope':'Exact finite regression only; universal proof is the accompanying Markdown lemma.'}
if __name__=='__main__':
 result=check();p=Path(__file__).with_name('FACTORIAL_RADIUS_CHECKS_OPTIMIZED.json' if sys.flags.optimize else 'FACTORIAL_RADIUS_CHECKS.json')
 p.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
