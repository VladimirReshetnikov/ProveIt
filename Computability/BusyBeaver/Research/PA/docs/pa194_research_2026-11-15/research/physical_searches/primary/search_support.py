#!/usr/bin/env python3
import json,time,itertools,collections
from pathlib import Path
import symbolic_runtime as s
P=Path(__file__).resolve().parent
rows={}
for ln in (P/'pa194.native.tm').read_text().splitlines():
 q,b,w,d,n=ln.split();rows[int(q),int(b)]=int(w),d=='R',int(n)
sites=json.loads((P/'sites.json').read_text()); ins=json.loads((P/'instructions.json').read_text())
cs=[]
for i,code in enumerate(ins):
 st=s.frame(tuple(map(int,sites[i][0])))
 f=lambda j,extra=0,effect=s.PLAIN:s.canonical(s.frame(tuple(map(int,sites[j][0])),extra,effect))
 if code[0]=='inc':
  _,r,n=code;cs.append((i,None,st,f(n,0,('x','inc',s.PHYSICAL[r]))))
 elif code[0]=='dec':
  _,r,z,p=code;cs.append((i,(s.PHYSICAL[r],True),st,f(z)));cs.append((i,(s.PHYSICAL[r],False),st,f(p,1,('x','dec',s.PHYSICAL[r]))))
 elif code[0]=='jump':cs.append((i,None,st,f(code[1])))
 else:cs.append((i,None,st,None))
byq=collections.defaultdict(set); snapshots={}
for k,c in enumerate(cs):
 def observe(st):
  byq[st[0]].add(k)
  if (k,st[0]) not in snapshots: snapshots[k,st[0]]=st
 if s.run(rows,c,observe=observe) is None:raise ValueError(c[:2])
print('collected',len(cs),'contracts',sum(map(len,byq.values())),'incidences',flush=True)
