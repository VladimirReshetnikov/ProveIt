#!/usr/bin/env python3
"""Independent literal stress check; not used as a universal induction premise."""
import json,random,sys
from pathlib import Path
from explore import T,B
from check_literal_instructions import read_table,paint,expected,program_sites,PHYSICAL
HERE=Path(__file__).resolve().parent

def execute(table,q,h,ones,steps):
 ones=set(ones)
 for _ in range(steps):
  w,d,q=table[q,int(h in ones)]
  if w:ones.add(h)
  else:ones.discard(h)
  h+=d
 return q,h,ones

def boot_frame(ones,h):
 if h-1 not in ones or any(x<h-1 for x in ones):return None
 right=sorted(x for x in ones if x>=h)
 if not right or right[0]-h<40:return None
 header=right[0];p=header+1;vals=[]
 while p+1 in ones:
  if p in ones:return None
  k=p+1
  while k in ones:k+=1
  vals.append(k-p-2);p=k
 if any(x>=p for x in ones):return None
 if len(vals)<10:return None
 return dict(head=h,gap=header-h,values=vals,last_spare_one=vals[-1]==1,dirty_formula_fields_zero=all(vals[PHYSICAL[r]]==0 for r in[1,2,5]))

out={};rng=random.Random(18631)
for borrow in [33,126]:
 table=read_table(HERE/f'borrowed_tail_{borrow}_partial.tm');count=0;total=0
 for r in range(9):
  for rep in range(100):
   vals=[rng.randrange(25)for _ in range(9+rng.randrange(1,5))];vals[-1]=1
   for mode in ['i','z','p']:
    v=vals.copy()
    if mode=='z':v[r]=0
    if mode=='p':v[r]=1+rng.randrange(25)
    word=list(B(v));word[sum(x+2 for x in v[:r])+1]='0';left={-i-1 for i in range(20) if rng.randrange(2)};initial=left|{i for i,b in enumerate(word)if b=='1'};result=v.copy();q=73 if mode=='i'else 95
    if mode=='i':result[r]+=1;result[-1]=0;result.append(1);steps=2*sum(x+2 for x in v)+7;qt,ht,origin,boundary=48,-1,0,set()
    elif mode=='z':steps=2*sum(x+2 for x in v[:r])+7;qt,ht,origin,boundary=112,-1,0,set()
    else:result[r]-=1;steps=2*sum(x+2 for x in v[:r])+4;qt,ht,origin,boundary=48,0,1,{0}
    got=execute(table,q,0,initial,steps);want=left|boundary|{origin+i for i,b in enumerate(B(result))if b=='1'}
    assert got==(qt,ht,want),(borrow,r,rep,mode,got[:2],sorted(got[2]^want));count+=1;total+=steps
 q,h,ones=95,0,set();frames=[]
 for step in range(1,1000001):
  w,d,q=table[q,int(h in ones)]
  if w:ones.add(h)
  else:ones.discard(h)
  h+=d
  if q==254:frames.append(dict(step=step,halt=True));break
  if q==96:
   frame=boot_frame(ones,h)
   if frame:frames.append(dict(step=step,**frame));break
 out[str(borrow)]=dict(local_stress_cases=count,literal_steps=total,status='PASS',bootstrap_search_bound=1000000,bootstrap_observations=frames,bootstrap_scope='Only a bounded literal search for an empty-PC, gap>=40 frame. No correctness transfer follows from one frame or failure to find one.')
(HERE/'borrowed_tail_literal_checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
