#!/usr/bin/env python3
"""Independent full-tape check of the temporary-tag 11-to-10 control.
This is a synthetic local gadget, not a ZFC machine or blank-start claim.
"""
import json
T={}
for q in [0,1,2,3,4,5,6,10,11,12,13]:
 for b in [0,1]:T[q,b]=(b,1,q)
for q,t in [(1,10),(2,11),(3,12),(4,13)]:T[q,0]=(0,1,t);T[q,1]=(1,1,0)
T[5,0]=(0,1,10);T[5,1]=(0,1,12);T[6,0]=(0,1,11);T[6,1]=(0,1,13)
def rename(q):return {2:1,4:3}.get(q,q)
M={(q,b):(w,d,rename(t)) for (q,b),(w,d,t)in T.items() if q not in [2,4]}
M[1,0]=(0,-1,999);M[3,0]=(1,-1,999);M[999,0]=(0,1,5);M[999,1]=(1,1,6)
def step(tab,cfg):
 q,h,ones=cfg;b=int(h in ones);w,d,q1=tab[q,b];ss=set(ones)
 if w:ss.add(h)
 else:ss.discard(h)
 return q1,h+d,frozenset(ss)
def exercise(tab):
 fails=0;cases=0
 for q in [1,2,3,4]:
  marker=int(q%2==0)
  for outer in range(8):
   ones={i for k,i in enumerate([-2,1,2])if(outer>>k)&1}
   if marker:ones.add(-1)
   old=step(T,(q,0,frozenset(ones)));new=(rename(q),0,frozenset(ones))
   for _ in range(3):new=step(tab,new)
   expected=(rename(old[0]),old[1],old[2]);cases+=1;fails+=new!=expected
 return cases,fails
cases,fails=exercise(M)
if fails:raise ValueError('positive control failed')
bad=dict(M);bad[999,1]=(1,1,5)
mutant_cases,mutant_fails=exercise(bad)
if mutant_fails==0:raise ValueError('bad selector escaped control')
bad2=dict(M);bad2[3,0]=(0,-1,999)
_,tag_fails=exercise(bad2)
if tag_fails==0:raise ValueError('erased pair tag escaped control')
print(json.dumps(dict(status='PASS',old_working_states=len({q for q,b in T}),new_working_states=len({q for q,b in M}),complete_local_cases=cases,new_steps=3,old_steps=1,bad_selector_failures=mutant_fails,erased_tag_failures=tag_fails),indent=2))
