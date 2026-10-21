#!/usr/bin/env python3
"""Independently check delivered input identities, source graphs, and grammar semantics.

This verifies finite data. It is not a runtime proof or a consistency proof.
"""
import json,hashlib,sys
from pathlib import Path
from model import *
P=Path(__file__).resolve().parent.parent
rows=json.loads((P/'inputs/sites218.json').read_text());t=parse(rows)
assert metrics(t)==dict(dag_nodes=205,leaf_occurrences=4744,maximum_depth=38,maximum_zero_run=6)
assert graph(rows)==arithmetic_graph(rows)
for p in sorted((P/'inputs').glob('*.tm')):
 T={};start=None
 for line in p.read_text().splitlines():
  if line.startswith('#! start '):start=int(line[9:]);continue
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();key=(int(q),int(b));assert key not in T;assert d in('L','R')and int(w)in(0,1);T[key]=(int(w),d,int(z))
 S={q for q,b in T};assert set(T)=={(q,b)for q in S for b in(0,1)};assert len(S)==218;assert {z for w,d,z in T.values()}-S=={254};assert start==0
 print('Table',p.name,'states',len(S),'sha256',hashlib.sha256(p.read_bytes()).hexdigest())
def pair_sig(aa,bb):
 la=len(aa)
 def tr(q,side):
  if q>=0:return q+(la if side else 0)
  if side==0:
   if q==-1:return la
   if q%2==0:return -1 if q==-2 else q+2
   return q
  if q < -1 and q%2:return 0 if q==-3 else q+2
  return q
 return tuple((o,r,tuple(tr(q,0)for q in ts))for o,r,ts in aa)+tuple((o,r,tuple(tr(q,1)for q in ts))for o,r,ts in bb)
for name in('open','prefix'):
 m=json.loads((P/'models'/name/'model.json').read_text());L={int(q):tuple(v)for q,v in m['leaves'].items()};sigs=[];productions=0
 for q,ps in enumerate(m['productions']):
  if q in L:assert not ps;sigs.append(localg(L[q]));continue
  assert ps and all(x<q and y<q for x,y in ps)
  x,y=ps[0];sigs.append(pair_sig(sigs[x],sigs[y]))
  for x,y in ps:assert pair_sig(sigs[x],sigs[y])==sigs[q];productions+=1
 assert sigs[m['root']]==localg(t);assert len(m['base'])+len(L)==205
 if name=='prefix':assert len(m['forced_prefix37'])==27
 print('Grammar',name,'classes',len(sigs),'productions',productions,'base DAG',len(m['base'])+len(L))
for p in sorted((P/'examples').glob('*/sites.json')):
 rr=json.loads(p.read_text());tt=parse(rr);assert graph(rr)==graph(rows)==arithmetic_graph(rr);assert metrics(tt)['dag_nodes']==205;assert metrics(tt)['maximum_zero_run']<=6;assert rr[:37]==rows[:37]
 print('Exploratory source',p.parent.name,metrics(tt))
print('All finite packet checks passed. No blank-tape <=217 result is claimed.')
