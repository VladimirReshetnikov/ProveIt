#!/usr/bin/env python3
"""Conservative exact215 context allocation, derived from context_allocate.py.
Keeps every retained row unchanged except dispatcher84; includes108's explicit
suffix precondition. New generic entries follow accepted215's checked choices.
Prefix and entry cost only; this is not a machine runtime/blank proof.
"""
import argparse,hashlib,json,sys,time
from collections import defaultdict,Counter
from functools import cache
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent/'vendor'))
import source_language as s
import build221 as b

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--seed',type=Path,required=True);ap.add_argument('--source',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--identity',action='store_true');a=ap.parse_args()
 a.output.mkdir(exist_ok=False);started=time.monotonic()
 sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
 assert sha(a.seed/'k215.native.tm')=='9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2'
 assert sha(a.seed/'sites215.json')=='17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba'
 old=s.tree(json.loads((a.seed/'sites215.json').read_text()));new=s.tree(json.loads(a.source.read_text()));T=b.read_table((a.seed/'k215.native.tm').read_bytes());groups,_=b.decoder_map(T,old)
 states=defaultdict(set)
 for q,ns in groups.items():
  for n in ns:states[n].add(q)
 counts=Counter();rejected=[]
 def leaf_context(q,n,p,bit):
  if q==108 and bit==1:
   op,arg=n[bit];suffix={('CC',2):'101',('CB',1):'001'}.get((op,arg))
   return suffix is not None and ('1'+p+'1').endswith(suffix)
  return True
 @cache
 def compatible(n,p,q):
  counts['compatible_calls']+=1
  if q not in states[n]:return False
  for bit in (0,1):
   if s.leaf(n[bit]):
    if not leaf_context(q,n,p,bit):return False
    continue
   tape={i:int(v) for i,v in enumerate(p+str(bit))};tape[-1]=1;before=dict(tape);h=len(p);state=q
   for _ in range(100):
    if h==len(p)+1:break
    if h not in tape:return False
    w,d,state=T[state,tape[h]];tape[h]=w;h+=d
   if h!=len(p)+1 or tape!=before or not compatible(n[bit],p+str(bit),state):return False
  return True
 leaf_actions={}
 for op in ('CI','CD','CC','CB','CH'):
  for arg in ([None] if op=='CH' else range(10)):
   lf=op,arg
   for bit in (0,1):
    choices=Counter(T[q,bit] for n,qs in states.items() for q in qs if n[bit]==lf)
    direct=[row for row in choices if row[:2]==(bit,1)]
    if len(direct)==1:leaf_actions[lf,bit]=direct[0]
    elif bit==1 and lf in {('CC',1),('CC',2),('CB',1)}:
     leaf_actions[lf,bit]=(0,-1,{('CC',1):1,('CC',2):16,('CB',1):302}[lf])
 U=dict(T);fresh0=max(300,max(q for q,_ in T)+1);fresh=fresh0;by_actions={};assignments=[];used=Counter()
 def go(n,p):
  nonlocal fresh
  assert not s.leaf(n)
  for q in sorted(states[n]):
   if q!=84 and compatible(n,p,q):used[q]+=1;return q
  if states[n]:rejected.append({'prefix':p,'states':sorted(states[n]),'leaf_count':len(s.sites(n))})
  rows=tuple(leaf_actions[n[bit],bit] if s.leaf(n[bit]) else (bit,1,go(n[bit],p+str(bit))) for bit in (0,1))
  if rows in by_actions:return by_actions[rows]
  q=fresh;fresh+=1;by_actions[rows]=q;U[q,0],U[q,1]=rows;assignments.append({'state':q,'prefix':p,'rows':rows});return q
 result={'scope':'Conservative prefix and literal-entry allocation only; no physical equivalence, primitive runtime or clean blank proof.',
  'source_sha256':sha(a.source),'source':str(a.source),'seed_table_sha256':sha(a.seed/'k215.native.tm'),'source_metrics':s.metrics(new)}
 try:
  for bit in (0,1):U[84,bit]=leaf_actions[new[bit],bit] if s.leaf(new[bit]) else (bit,1,go(new[bit],str(bit)))
  reach={0};todo=[0]
  for q in todo:
   for bit in (0,1):
    z=U[q,bit][2]
    if z!=254 and z not in reach:reach.add(z);todo.append(z)
  U={k:v for k,v in U.items() if k[0] in reach};gg,gp=b.decoder_map(U,new)
  for q,ns in gg.items():
   if q in groups and q!=84:assert ns<=groups[q],('old binding',q)
  assert all(U[q,bit]==T[q,bit] for q in reach if q<fresh0 and q!=84 for bit in (0,1))
  leaves=0;prefixes=0;local108=0
  for q,ps in gp.items():
   for p in ps:
    prefixes+=1;n=s.subtree(new,p);tape={-1:1,**{i:int(v) for i,v in enumerate(p)}};before=dict(tape);h=0;z=84
    for _ in range(10000):
     if h==len(p):break
     assert h in tape;w,d,z=U[z,tape[h]];tape[h]=w;h+=d
    assert (h,z,tape)==(len(p),q,before)
    for bit,ch in enumerate(n):
     if not s.leaf(ch):continue
     leaves+=1
     if q<fresh0 and q!=84:
      assert U[q,bit]==T[q,bit] and leaf_context(q,n,p,bit)
      local108+=int(q==108 and bit==1)
     else:assert U[q,bit]==leaf_actions[ch,bit]
  assert leaves==len(s.sites(new)) and prefixes==leaves-1
  if a.identity:assert new==old and U==T and b.table_bytes(U)==(a.seed/'k215.native.tm').read_bytes()
  raw=b.table_bytes(U);(a.output/'prefix-only.native.tm').write_bytes(raw)
  result.update(status='PREFIX_AND_ENTRY_PASS',states=len(U)//2,rows=len(U),fresh=fresh-fresh0,retired=sorted({q for q,_ in T}-reach),
   internal_prefixes=prefixes,leaf_entries=leaves,local108_entries=local108,literal_identity_control=a.identity,table_sha256=hashlib.sha256(raw).hexdigest())
 except (AssertionError,ValueError,KeyError) as e:result.update(status='REJECTED',error=repr(e))
 result.update(seconds=time.monotonic()-started,assignments=assignments,rejected_old_contexts=rejected,counts=dict(counts))
 (a.output/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ('assignments','rejected_old_contexts')},indent=2))
 if result['status']=='REJECTED':raise SystemExit(1)
if __name__=='__main__':main()
