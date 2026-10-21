#!/usr/bin/env python3
"""Owned exact finite base certificate for CONSTANT_BIAS_CREDIT_THEOREM.md."""
import json,math
from pathlib import Path
import argparse
ap=argparse.ArgumentParser();ap.add_argument("--out",type=Path,required=True);args=ap.parse_args();args.out.mkdir(parents=True,exist_ok=True)
if not __debug__:raise SystemExit("Assertions required")

def unpair(n):
 s=(math.isqrt(8*n+1)-1)//2;y=n-s*(s+1)//2
 return s-y,y

def word(n):
 out=[];r=n;first=True
 while first or r:
  first=False;a,r=unpair(r)
  if a==0:out.append('S')
  elif a==1:_,r=unpair(r);out.append('MP')
  else:_,r=unpair(r);_,r=unpair(r);out.append('AX')
 return out

def main():
 if not __debug__:raise RuntimeError('Assertions must be enabled')
 end={};path={};cases=[];worst=0;witness=None
 for n in range(1,64):
  if n==1:initial=0;route=[]
  else:
   p=min((p for p in (n-1,n-2) if p in end),key=lambda p:end[p])
   initial=end[p];route=path[p]
  running=initial;low=running;w=word(n)
  for i,c in enumerate(w):
   running+= {'S':-1,'MP':0,'AX':10}[c];low=min(low,running)
   if running<worst:worst=running;witness={'candidate':n,'command_index':i,'candidate_path':route+[n]}
  end[n]=running;path[n]=route+[n]
  cases.append({'candidate':n,'word':w,'minimum_entry_balance':initial,'minimum_internal_balance':low,'minimum_exit_balance':running})
 assert worst==-3
 odd_balance=0;odd_minimum=0;odd_cases=[]
 for n in range(1,64,2):
  entry=odd_balance
  for c in word(n):
   odd_balance+={'S':-1,'MP':0,'AX':10}[c]
   odd_minimum=min(odd_minimum,odd_balance)
  odd_cases.append({'candidate':n,'entry_balance':entry,'exit_balance':odd_balance})
 assert odd_minimum==0
 odd={'status':'ODD_SCHEDULE_FINITE_BASE_PASS','minimum_balance':odd_minimum,'final_balance':odd_balance,'cases':odd_cases}
 args.out.joinpath('ODD_SCHEDULE_BASE.json').write_text(json.dumps(odd,indent=2)+'\n')
 counts=[];cumulative=0
 for n in range(200000):
  a,y=unpair(n)
  if a==0:v=1+(counts[y] if y else 0)
  else:
   z=unpair(y)[1] if a==1 else unpair(unpair(y)[1])[1]
   v=counts[z] if z else 0
  counts.append(v);cumulative+=v
  assert cumulative<=n+1
  if n<64:assert v==word(n).count('S')
 corroboration={'status':'COUNTING_BOUND_FINITE_CORROBORATION_PASS','candidates':len(counts),'S_occurrences':cumulative,'scope':'Finite independent recurrence check only; analytic proof supplies the infinite theorem.'}
 args.out.joinpath('COUNTING_BOUND_CORROBORATION.json').write_text(json.dumps(corroboration,indent=2)+'\n')
 out={'status':'FINITE_CREDIT_BASE_PASS','scope':'All finite schedules starting at 1 with gaps 1 or 2 through candidate 63; the infinite extension requires the published analytic bound. No actual binary source binding is asserted.','minimum_balance':worst,'witness':witness,'cases':cases}
 args.out.joinpath('DENSITY_CREDIT_BASE.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='cases'}))
if __name__=='__main__':main()
