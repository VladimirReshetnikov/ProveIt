#!/usr/bin/env python3
"""Machine-graph nonisomorphism, not a claim of a new logical calculus."""
from collections import Counter,deque
import json,hashlib
from pathlib import Path
from reconstruct import table
ROOT=Path(__file__).resolve().parent.parent
def compare(A,B):
 todo=deque([(0,0,'')]);mp={};rev={};failure=None
 while todo:
  a,b,p=todo.popleft()
  if a in mp:
   if mp[a]!=b:failure=dict(kind='inconsistent_mapping',path=p);break
   continue
  if b in rev:failure=dict(kind='noninjective_mapping',path=p);break
  mp[a]=b;rev[b]=a
  if(a==254)!=(b==254):failure=dict(kind='halt_mismatch',path=p);break
  if a==254:continue
  for bit in(0,1):
   x,y=A[a,bit],B[b,bit]
   if x[:2]!=y[:2]:failure=dict(kind='output_mismatch',path=p+str(bit),old=x,new=y);break
   todo.append((x[2],y[2],p+str(bit)))
  if failure:break
 assert failure
 ts=[A,B];colors=[{q:int(q==254)for q in{q for q,b in t}|{254}}for t in ts];separation=None
 for iteration in range(216):
  ss=[{q:('halt',)if q==254 else('state',)+tuple((t[q,b][0],t[q,b][1],c[t[q,b][2]])for b in(0,1))for q in c}for t,c in zip(ts,colors)]
  lookup={s:i for i,s in enumerate(sorted(set(ss[0].values())|set(ss[1].values()),key=repr))};colors=[{q:lookup[s]for q,s in z.items()}for z in ss];hist=[Counter(c.values())for c in colors]
  if hist[0]!=hist[1]:separation=dict(round=iteration+1,histograms=[dict(h)for h in hist]);break
 assert separation
 return dict(rooted_nonisomorphism=failure,unrooted_nonisomorphism=separation,changed_rows=[dict(row=k,old=A.get(k),new=B.get(k))for k in sorted(A.keys()|B.keys())if A.get(k)!=B.get(k)])
def check(parent):
 raw=ROOT/'provenance/published11_134.original.native.tm';meta=json.loads((ROOT/'provenance/published11_134_mapping.json').read_text());assert hashlib.sha256(raw.read_bytes()).hexdigest()==meta['original_table_sha256'];mp={int(k):v for k,v in meta['original_to_comparison'].items()};assert len(mp)==len(set(mp.values()))==216 and mp[0]==0 and mp[254]==254;T=table(raw);assert {(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in T.items()}==table(ROOT/'provenance/published11_134.native.tm')
 U=table(ROOT/'machine/k215.native.tm');return {n:compare(table(p),U)for n,p in [('delivered210',parent/'machine/k215.native.tm'),('delivered120',parent/'secondary/machine/k215.native.tm'),('published11_134',ROOT/'provenance/published11_134.native.tm')]}
