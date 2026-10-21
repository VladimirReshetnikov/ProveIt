#!/usr/bin/env python3
"""Owned independent checker for the full-tape inductive context certificates."""
from pathlib import Path
import json
D=Path(__file__).parent
assert __debug__
for directory in sorted(p for p in D.iterdir()if p.is_dir()):
 words=iter(map(int,(directory/'fold.in').read_text().split()));n=next(words);num_pairs=next(words);start=next(words);T={};contexts={}
 for _ in range(n):
  q=next(words)
  for b in(0,1):T[q,b]=tuple(next(words)for _ in range(3))
  k=next(words);contexts[q]={next(words)for _ in range(k)};assert len(contexts[q])==k
 pairs=[tuple(next(words)for _ in range(3))for _ in range(num_pairs)];assert list(words)==[]
 info=json.loads((directory/'FOLD_INPUT.json').read_text());width=info['width'];r=width//2;mask=(1<<width)-1
 assert start==info['initial_state'] and contexts[start]==set(range(1<<width));assert len(T)==2*n
 assert sum(map(len,contexts.values()))<=info['context_points']
 checks=0
 for q,ws in contexts.items():
  for x in ws:
   w,d,z=T[q,(x>>r)&1];assert d in(-1,1)and w in(0,1)
   y=(x&~(1<<r))|(w<<r)
   for b in(0,1):
    new=((y>>1)|(b<<(width-1)))if d==1 else((y<<1)&mask)|b
    if z!=254:assert new in contexts[z]
    checks+=1
 assert checks==info['closure_checks']
 expected=[]
 for drop in sorted(contexts):
  if drop==start:continue
  for keep in sorted(contexts):
   if drop==keep:continue
   phi=lambda z:keep if z==drop else z
   same=[b for b in(0,1)if T[drop,b][:2]+(phi(T[drop,b][2]),)==T[keep,b][:2]+(phi(T[keep,b][2]),)]
   if len(same)==1:expected.append((drop,keep,same[0]))
 assert pairs==expected
 result=(directory/'fold_both.log').read_text().strip().splitlines();assert len(result)==1 and result[0].startswith('DONE ')
 _,ordered,actions,hits=result[0].split();assert int(ordered)==(n-1)*(n-1) and int(hits)==0
 print(directory.name,'CONTEXT_PASS',n,width,'logged branch tests',actions)
print('All contexts inductively valid. Logged zero survivors are replayed only by running the supplied C++ searches.')
