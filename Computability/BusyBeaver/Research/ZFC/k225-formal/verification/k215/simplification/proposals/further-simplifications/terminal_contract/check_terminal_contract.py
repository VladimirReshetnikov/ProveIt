#!/usr/bin/env python3
"""Finite corroboration of a mathematical theorem, not a kernel proof."""
import sys,itertools,json,hashlib
from pathlib import Path
if not __debug__ or sys.flags.optimize: raise SystemExit('Optimization is forbidden')
D=Path(__file__).resolve().parent

def halts(t,a):
 seen=set()
 while a is not None:
  if a in seen:return False
  seen.add(a);a=t[a]
 return True

def positive_reach(t,b):
 seen=set();b=t[b]
 while b is not None and b not in seen:
  seen.add(b);b=t[b]
 return seen

def predicates(a,b,r,zero=False):
 advance=all(a[x] is None or any((a[x],y1) in r for y1 in positive_reach(b,y)|({y} if zero else set())) for x,y in r)
 drain=all(a[x] is not None or halts(b,y) for x,y in r)
 strict=all((a[x] is None)==(b[y] is None) for x,y in r)
 return advance,drain,strict

def main():
 total=advance_ok=both_ok=relaxed_only=0
 for a in itertools.product((None,0,1),repeat=2):
  for b in itertools.product((None,0,1,2),repeat=3):
   for mask in range(64):
    r={(x,y)for x in range(2)for y in range(3)if mask>>(3*x+y)&1}
    total+=1;advance,drain,strict=predicates(a,b,r)
    if advance:
     advance_ok+=1
     assert all(not halts(b,y) or halts(a,x) for x,y in r)
    if advance and drain:
     both_ok+=1
     assert all(halts(a,x)==halts(b,y) for x,y in r)
     relaxed_only+=not strict
 # Terminal cleanup allowed, while immediate terminal equivalence fails.
 assert predicates((None,),(1,None),{(0,0)})==(True,True,False)
 # Removing positive progress admits a looping source against a halted target.
 assert predicates((0,),(None,),{(0,0)},True)[:2]==(True,True)
 assert not halts((0,),0) and halts((None,),0)
 # Source halt must still imply target termination.
 assert predicates((None,),(0,),{(0,0)})[:2]==(True,False)
 out={'status':'PASS_FINITE_CORROBORATION_NOT_KERNEL_PROOF','source_states':2,'target_states':3,'systems_and_relations':total,'advance_holds':advance_ok,'advance_and_terminal_drain_hold':both_ok,'valid_relaxed_not_strict_terminal_agreement':relaxed_only,'terminal_cleanup_example':True,'zero_progress_counterexample':True,'missing_terminal_drain_counterexample':True,'formal_draft_compiled':False}
 print(json.dumps(out,indent=2))
if __name__=='__main__':main()
