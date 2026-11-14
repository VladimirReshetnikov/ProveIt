#!/usr/bin/env python3
"""Pair/old-row quotients of fresh PA194NQ, preserving protected arithmetic controls."""
from pathlib import Path
import sys,itertools,json,time,hashlib,collections
ROOT=Path(__file__).resolve().parent.parent
P=ROOT/'machine'
BASE=ROOT/'construction'
sys.path.insert(0,str(BASE))
import symbolic_runtime as s
rows={}
for line in (P/'machine.native.tm').read_text().splitlines():
 q,b,w,d,n=line.split();rows[int(q),int(b)]=int(w),d=='R',int(n)
sites=[(tuple(map(int,p)),op,a)for p,op,a in json.loads((P/'sites.json').read_text())]
ins=json.loads((P/'instructions.json').read_text())
cs=[]
for i,code in enumerate(ins):
 st=s.frame(sites[i][0])
 if code[0]=='inc':
  _,r,n=code;cs.append((i,None,st,s.canonical(s.frame(sites[n][0],0,('x','inc',s.PHYSICAL[r])))))
 elif code[0]=='dec':
  _,r,z,p=code
  cs.append((i,(s.PHYSICAL[r],True),st,s.canonical(s.frame(sites[z][0]))))
  cs.append((i,(s.PHYSICAL[r],False),st,s.canonical(s.frame(sites[p][0],1,('x','dec',s.PHYSICAL[r])))))
 elif code[0]=='jump':cs.append((i,None,st,s.canonical(s.frame(sites[code[1]][0]))))
 else:assert code==['halt'];cs.append((i,None,st,None))
states=sorted({qfor for qfor,b in rows});non=[q for q in states if q not in s.BOXSTATES]
assert len(states)==194 and len(non)==171 and len(cs)==4755
cover=collections.defaultdict(set)
branch_cover=collections.defaultdict(set)
for i,con in enumerate(cs):
 def observe(st):
  cover[st[0]].add(i)
  if not st[1]:
   bit=s.headbit(st[3])
   if bit is not None:branch_cover[st[0],bit].add(i)
 v=s.run(rows,con,observe=observe)
 assert v is not None,(i,con[0])
print('baseline',len(cs),'nonprotected',len(non),flush=True)
start=time.time();survivors=[];count=0
for a,b in itertools.combinations(non,2):
 quick={min(branch_cover[q,bit]) for q in (a,b) for bit in (0,1) if branch_cover[q,bit]}
 todo=sorted(quick)+sorted((cover[a]|cover[b])-quick)
 for pick in itertools.product((a,b),repeat=2):
  count+=1
  table={(q,bit):(w,d,b if n==a else n)for(q,bit),(w,d,n)in rows.items()if q!=a}
  for bit in(0,1):
   w,d,n=rows[pick[bit],bit];table[b,bit]=(w,d,b if n==a else n)
  fail=None
  for i in todo:
   if s.run(table,cs[i])is None:fail=i;break
  if fail is None:
   print('SURVIVE',a,b,pick,flush=True);survivors.append([a,b,pick])
 if count%1000<4:print('progress',count,'seconds',round(time.time()-start,2),flush=True)
result=dict(candidates=count,nonprotected_controls=len(non),survivors=survivors,
  source_sites=len(sites),source_contracts=len(cs),symbolic_bound=1024,
  machine_native_sha256=hashlib.sha256((P/'machine.native.tm').read_bytes()).hexdigest(),
  seconds=time.time()-start,
  scope='Exact pair/old-row quotient family, all affected arbitrary-register source contracts; failure of bounded symbolic method is not a semantic counterexample or lower bound')
(ROOT/'search/nq_pairs_result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2),flush=True)
