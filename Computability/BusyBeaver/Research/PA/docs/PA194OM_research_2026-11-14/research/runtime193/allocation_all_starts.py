#!/usr/bin/env python3
"""Exact all-start/all-allocation obstruction for the specified runtime193.

No finite fuel cut is used as a divergence certificate. Every branch ends in
literal halt or a certified outward monotone zero-reading ray. Initial blank
prefixes that never write1 are certified separately by a zero-row cycle.
Only the eleven displayed selector targets are permuted. No general193-state
lower bound and no obstruction to other bootstrap or representation edits.
"""
from pathlib import Path
from collections import Counter
from math import factorial
import argparse,hashlib,json
HERE=Path(__file__).resolve().parent
EXPECTED='50f7be44afb63293365270a83111299247d12d140614e4b4c9a52786163acb53'
SK=(51,36,25,48,32,33,22,55,60)
SELECTORS={(14,1):6,(17,1):4,(21,1):8,(39,1):1,(41,1):2,(45,1):7,
           (56,1):0,(61,1):2,(82,1):5,(144,1):3,(161,1):4}

def table():
 text=(HERE/'runtime193.native.tm').read_bytes()
 assert hashlib.sha256(text).hexdigest()==EXPECTED
 T={}
 for line in text.decode().splitlines():
  q,b,w,d,n=line.split();T[int(q),int(b)]=(int(w),1 if d=='R'else-1,int(n))
 assert len(T)==386 and len({q for q,b in T})==193
 assert {(q,b):SK.index(n)for(q,b),(w,d,n)in T.items()if n in SK and q not in SK and q!=88}==SELECTORS
 return T

def ray_certificate(T,q):
 """A fixed-direction zero-row path with a closed eventual control cycle."""
 vis={};path=[];direction=None
 while q in {x for x,b in T} and q not in vis:
  vis[q]=len(path);w,d,n=T[q,0]
  if direction is not None and d!=direction:return None
  direction=d;path.append([q,0,w,d,n]);q=n
 if q not in vis:return None
 return dict(direction=direction,path=path,cycle_start=vis[q])

def run():
 T=table();qs=sorted({q for q,b in T});rays={q:r for q in qs if(r:=ray_certificate(T,q))is not None}
 prefixes=[];groups=Counter()
 for start in qs:
  q=start;h=0;vis={};path=[]
  while q!=254 and q not in vis and T[q,0][0]==0:
   vis[q]=len(path);w,d,n=T[q,0];path.append([q,0,w,d,n]);h+=d;q=n
  if q==254:kind='halt_without_write'
  elif q in vis:kind='zero_cycle'
  else:kind='first_writer'
  rec=dict(start=start,kind=kind,steps=len(path),translation=h,state=q,path=path)
  if kind=='zero_cycle':rec['cycle_start']=vis[q]
  prefixes.append(rec);groups[q if kind=='first_writer'else kind]+=1
 assert groups==Counter({35:169,'zero_cycle':10,4:5,16:2,74:2,66:2,0:1,97:1,198:1})
 leaves=[]
 def simulate(start,q,h,ones,mapping,step,peak):
  # Guard only catches a code regression; successful certification has no caps.
  while step<=1000:
   peak=max(peak,len(ones))
   if q==254:kind='halt';break
   cert=rays.get(q)
   if cert and h not in ones and(not ones or(cert['direction']>0 and h>max(ones))or(cert['direction']<0 and h<min(ones))):kind='outward_ray';break
   b=int(h in ones);w,d,n=T[q,b]
   if(q,b)in SELECTORS:
    slot=SELECTORS[q,b]
    if slot not in mapping:
     for target in range(9):
      if target in mapping.values():continue
      newmap=dict(mapping);newmap[slot]=target;newones=set(ones)
      (newones.add if w else newones.discard)(h)
      simulate(start,SK[target],h+d,newones,newmap,step+1,peak)
     return
    n=SK[mapping[slot]]
   (ones.add if w else ones.discard)(h);h+=d;q=n;step+=1
  else:raise AssertionError('Uncertified leaf; no theorem is emitted')
  assert peak<12 # No complete source frame before the terminal certificate.
  rec=dict(start=start,allocation=sorted(mapping.items()),kind=kind,steps=step,state=q,head=h,ones=sorted(ones),peak_ones=peak,permutation_completions=factorial(9-len(mapping)))
  if kind=='outward_ray':rec['ray']=rays[q]
  leaves.append(rec)
 for q in sorted(x for x in groups if isinstance(x,int)):
  simulate(q,q,0,set(),{},0,0)
 assert len(leaves)==16
 total=Counter();maxclock=0
 for pref in prefixes:
  if pref['kind']=='zero_cycle':total['zero_cycle']+=factorial(9);maxclock=max(maxclock,pref['steps']);continue
  assert pref['kind']=='first_writer'
  selected=[leaf for leaf in leaves if leaf['start']==pref['state']]
  assert sum(x['permutation_completions']for x in selected)==factorial(9)
  for leaf in selected:
   total[leaf['kind']]+=leaf['permutation_completions'];maxclock=max(maxclock,pref['steps']+leaf['steps'])
 assert total==Counter(halt=725760,zero_cycle=3628800,outward_ray=65681280)
 assert sum(total.values())==193*factorial(9)==70035840 and maxclock==94
 return dict(table_sha256=EXPECTED,working_states=193,allocations=factorial(9),state_allocation_pairs=70035840,
             classifications=dict(total),maximum_certificate_clock=maxclock,maximum_prefix_ones=max(x['peak_ones']for x in leaves),
             essential_first_writers=8,adaptive_allocation_leaves=16,selector_rows=[[q,b,k]for(q,b),k in SELECTORS.items()],
             prefixes=prefixes,leaves=leaves,
             scope='Only eleven external selector targets are permuted; 301->88 runtime core fixed. All193 initial controls, blank zero tape. No lower bound on other machines.')

if __name__=='__main__':
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--write',type=Path);a=ap.parse_args()
 if not __debug__:raise SystemExit('Assertions must be enabled')
 result=json.loads(json.dumps(run()))
 if a.write:a.write.write_text(json.dumps(result,indent=2)+'\n')
 else:
  expected=json.loads((HERE/'allocation_all_starts.json').read_text());assert result==expected
 print(json.dumps({k:v for k,v in result.items()if k not in('prefixes','leaves','selector_rows')},indent=2))
