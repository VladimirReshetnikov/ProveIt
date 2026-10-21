#!/usr/bin/env python3
"""Reconstruct the selected scanner-aware sources and independently check their CFGs.

Use the supplied baseline source, a rotation-result JSON, and the selected source.
No source-search implementation is imported or executed.
"""
from pathlib import Path
from functools import lru_cache
import argparse,hashlib,json

def freeze(t):return tuple(map(freeze,t))if isinstance(t,list)else t
def leaf(t):return isinstance(t[0],str)
def parse(rows):
 entries={p:(op,a)for p,op,a in rows};assert len(entries)==len(rows)
 def visit(p):
  if p in entries:return entries[p]
  assert any(x.startswith(p+'0')for x in entries)and any(x.startswith(p+'1')for x in entries)
  return visit(p+'0'),visit(p+'1')
 return visit('')
def rows(t,p=''):
 return [[p,*t]]if leaf(t)else rows(t[0],p+'0')+rows(t[1],p+'1')
def replace(t,o,n):
 if t==o:return n
 return t if leaf(t)else(replace(t[0],o,n),replace(t[1],o,n))
def count(t):
 seen=set()
 def go(n):
  if n in seen:return
  seen.add(n)
  if not leaf(n):go(n[0]);go(n[1])
 go(t);return len(seen)
def cfg(ss):
 leaves={p:i for i,(p,op,a)in enumerate(ss)};interval={}
 def visit(p):
  if p in leaves:ans=(leaves[p],leaves[p]+1)
  else:
   l=visit(p+'0');r=visit(p+'1');assert l[1]==r[0];ans=(l[0],r[1])
  interval[p]=ans;return ans
 visit('')
 def cut(p,b,n):
  for i in range(len(p)-1,-1,-1):
   if p[i]==b:
    n-=1
    if n==0:return interval[p[:i]][1]%len(ss)if b=='0'else interval[p[:i]][0]
  return 0
 ans=[]
 for i,(p,op,a)in enumerate(ss):
  targets=[(i+1)%len(ss)]if op=='CI'else[cut(p,'0',1),(i+1)%len(ss)]if op=='CD'else[cut(p,'0',a)]if op=='CB'else[cut(p,'1',a)]if op=='CC'else[]
  ans.append([op,a,targets])
 return ans
def direct_cfg(ss):
 codes={p:i for i,(p,op,a)in enumerate(ss)}
 def locate(p):
  for i in range(1,len(p)+1):
   if p[:i]in codes:assert '1'not in p[i:];return codes[p[:i]]
  p=p or ''
  while p not in codes:p+='0'
  return codes[p]
 def inc(p):return format((int(p,2)+1)%(1<<len(p)),f'0{len(p)}b')if p else ''
 def cut(p,b,n):
  x=[i for i,c in enumerate(p)if c==b];return p[:x[-n]]if len(x)>=n else''
 ans=[]
 for p,op,a in ss:
  ts=[locate(inc(p))]if op=='CI'else[locate(inc(cut(p,'0',1))),locate(inc(p))]if op=='CD'else[locate(inc(cut(p,'0',a)))]if op=='CB'else[locate(cut(p,'1',a))]if op=='CC'else[]
  ans.append([op,a,ts])
 return ans
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('baseline',type=Path);a.add_argument('recipe',type=Path);a.add_argument('candidate',type=Path);ar=a.parse_args();old=json.loads(ar.baseline.read_text());t=parse(old);r=json.loads(ar.recipe.read_text());assert hashlib.sha256(ar.baseline.read_bytes()).hexdigest()==r['source_sha256']
 for j,x in enumerate(r['chain']):
  o=freeze(x['old']);n=freeze(x['new']);assert not leaf(o)
  if x['direction']=='R':assert not leaf(o[0])and n==(o[0][0],(o[0][1],o[1]))
  else:assert x['direction']=='L'and not leaf(o[1])and n==((o[0],o[1][0]),o[1][1])
  t2=replace(t,o,n);assert t2!=t;t=t2
 selected=json.loads(ar.candidate.read_text());assert rows(t)==selected
 assert [x[1:]for x in old]==[x[1:]for x in selected]
 assert cfg(old)==direct_cfg(old)==cfg(selected)==direct_cfg(selected)
 maximum=max(len(z)for p,op,a in selected for z in p.split('1'));assert maximum==5
 print(json.dumps(dict(status='SOURCE_ROTATION_AND_BOTH_CFGS_PASS',dag_nodes=count(t),leaf_occurrences=len(selected),maximum_zero_run=maximum,rotation_steps=len(r['chain']),baseline_sha256=hashlib.sha256(ar.baseline.read_bytes()).hexdigest(),candidate_sha256=hashlib.sha256(ar.candidate.read_bytes()).hexdigest(),scope='Exact source-only result; no allocated binary table, startup proof, or smaller state-count claim.'),indent=2))
