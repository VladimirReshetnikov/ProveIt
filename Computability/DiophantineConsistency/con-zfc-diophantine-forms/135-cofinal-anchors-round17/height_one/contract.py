#!/usr/bin/env python3
"""Incidence-local alias contraction, with exact coefficient aggregation.

A generalization of the shared-incidence compiler in vendor/build.py.
No global C4 restriction: only coefficients occurring in the actual energy
matter. Each accepted merge identifies aliases of the same logical value.
"""
from collections import defaultdict, Counter
from copy import deepcopy
import argparse, hashlib, json, random, sys, time
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'vendor'))
import build

def write(p,x):
 p.parent.mkdir(parents=True,exist_ok=True); p.write_text(json.dumps(x,sort_keys=True,separators=(',',':'))+'\n')

def energy(cert):
 pol={}; inc=[[] for _ in cert['vertices']]
 def add(c,m):
  m=tuple(sorted(m)); v=pol.get(m,0)+c
  if v: pol[m]=v
  else: pol.pop(m,None)
 for e in cert['edges']:
  m=e['monomial']; c=e['coefficient']; add(1,m+m)
  inc[e['tail']].append((c,m)); inc[e['head']].append((-c,m))
 for es in inc:
  for j,(c,m) in enumerate(es):
   for d,n in es[j+1:]: add(c*d,m+n)
 return pol

class LocalContraction:
 def __init__(self, pol):
  self.pol=pol.copy(); self.index=defaultdict(set); self.parent={}; self.accepted=0; self.attempts=0
  for m in pol:
   for v in set(m): self.index[v].add(m)
 def merge(self,a,b):
  self.attempts+=1
  affected=self.index[b]
  changes=defaultdict(int)
  for m in affected:
   c=self.pol[m]; changes[m]-=c; n=tuple(sorted(a if v==b else v for v in m)); changes[n]+=c
  if any(abs(self.pol.get(m,0)+c)>1 for m,c in changes.items()): return False
  for m,c in changes.items():
   if not c: continue
   old=self.pol.get(m,0); new=old+c
   if old:
    for v in set(m): self.index[v].remove(m)
   if new:
    self.pol[m]=new
    for v in set(m): self.index[v].add(m)
   else: self.pol.pop(m,None)
  self.parent[b]=a; self.accepted+=1
  return True
 def root(self,v):
  while v in self.parent: v=self.parent[v]
  return v

def contract(source,hubs=128,seed=0,rounds=3):
 initial,old=build.compile_graph(source,hubs,True)
 pol=energy(old); lc=LocalContraction(pol)
 logical=defaultdict(list)
 for i,d in enumerate(initial['variables']):
  if d['kind'] in ('private','shared','unit_shared'):
   logical[d.get('normalized_variable')].append(i)
 rng=random.Random(seed)
 # Mix class order because quartic collisions couple logical classes.
 classes=sorted(logical,key=lambda v:(-len(logical[v]),v if v is not None else -1))
 if seed: rng.shuffle(classes)
 history=[]
 for sweep in range(rounds):
  before=lc.accepted
  for v in classes:
   ids=list(dict.fromkeys(lc.root(i) for i in logical[v]))
   # Put a high-degree representative first, but merge low-degree aliases first.
   ids.sort(key=lambda i:(-len(lc.index[i]),i))
   if seed: rng.shuffle(ids)
   live=[]
   for b in ids:
    opts=sorted(live,key=lambda a:(-len(lc.index[a]),a))
    if not any(lc.merge(a,b) for a in opts): live.append(b)
  history.append(lc.accepted-before)
  if not history[-1]: break
 newvars=[]; rename={}; representatives={}; groups=defaultdict(list)
 for i,d in enumerate(initial['variables']):
  if d['kind'] in ('equality_dummy','unit_dummy'): continue
  root=lc.root(i)
  if root not in representatives:
   n=len(newvars); representatives[root]=n
   if d['kind']=='flow': nd=deepcopy(d)
   else: nd={'kind':'alias','normalized_variable':d.get('normalized_variable')}
   newvars.append(nd)
   if nd['kind']=='alias': groups[nd['normalized_variable']].append(n)
  rename[i]=representatives[root]
 cert=deepcopy(old)
 for p in cert['products']: p['factors']=[rename[i] for i in p['factors']]
 for e in cert['edges']: e['monomial']=[rename[i] for i in e['monomial']]
 cert['schema']='incidence-local-height-one-certificate-v1'
 cert['equality_cycles']=[]
 square_aliases={p['factors'][0] for p in cert['products'] if p['factors'][0]==p['factors'][1]}
 for v,ids in sorted(groups.items(),key=lambda kv: (-1 if kv[0] is None else kv[0])):
  if v is None: continue
  mode='quartic_pair' if len(ids)==2 and not square_aliases.intersection(ids) else 'cycle'
  if len(ids)==2 and mode=='cycle':
   ids.append(len(newvars)); newvars.append({'kind':'equality_dummy','normalized_variable':v})
  cert['equality_cycles'].append({'normalized_variable':v,'aliases':ids,'mode':mode})
 units=groups[None]
 while len(units)<2:
  units.append(len(newvars)); newvars.append({'kind':'unit_dummy'})
 cert['unit_path']=units
 epol=energy(cert)
 projected={tuple(sorted(rename[i] for i in m)):c for m,c in lc.pol.items()}
 if projected!=epol: raise ValueError('Contraction reconstruction failure')
 def add(c,m):
  m=tuple(sorted(m)); z=epol.get(m,0)+c
  if z: epol[m]=z
  else: epol.pop(m,None)
 for cy in cert['equality_cycles']:
  ids=cy['aliases']
  if cy['mode']=='quartic_pair':
   a,b=ids; add(1,[a,a,a,a]); add(1,[b,b,b,b]); add(-1,[a,a,a,b]); add(-1,[a,b,b,b]); continue
  if len(ids)==1: continue
  for i in ids: add(1,[i,i])
  for a,b in zip(ids,ids[1:]+ids[:1]): add(-1,[a,b])
 add(1,[])
 for u in units: add(1,[u,u])
 for a,b in zip(units,units[1:]): add(-1,[a,b])
 add(-1,[units[0]]); add(-1,[units[-1]])
 if any(abs(c)!=1 for c in epol.values()): raise ValueError('Height failure')
 used={v for m in epol for v in m}
 if used!=set(range(len(newvars))): raise ValueError('Unused coordinate')
 metrics={'variables':len(newvars),'degree':max(map(len,epol)),'monomials':len(epol),'coefficient_height':1,
 'individual_degree':max(max(Counter(m).values()) for m in epol if m),'constant':epol[()],
 'source_variables':len(source['variables']),'source_rows':len(source['residuals']),
 'normalized_variables':len(cert['normalization']['variables']),'normalized_rows':len(cert['normalization']['rows']),
 'occurrences':len(cert['products']),'flow_variables':sum(d['kind']=='flow' for d in newvars),
 'equality_dummies':sum(d['kind']=='equality_dummy' for d in newvars),'unit_coordinates':len(units),
 'alias_coordinates':sum(d['kind']=='alias' for d in newvars),'hubs':hubs,
 'quartic_pair_classes':sum(cy['mode']=='quartic_pair' for cy in cert['equality_cycles']),
 'positive_coefficients':sum(c==1 for c in epol.values()),'negative_coefficients':sum(c==-1 for c in epol.values())}
 artifact={'schema':'incidence-local-height-one-quartic-v1','domain':'unrestricted integers','variables':newvars,'metrics':metrics,
 'terms':[[epol[m],list(m)] for m in sorted(epol,key=lambda m:(len(m),m))]}
 cert['contraction']={'seed':seed,'rounds':len(history),'accepted_by_round':history,'attempts':lc.attempts,
 'initial_variables':len(initial['variables']),'initial_monomials':len(initial['terms']),
 'initial_aliases':sum(len(a) for a in logical.values()),'merged_aliases':lc.accepted,
 'root_map':[[i,rename[i]] for i in sorted(rename)]}
 return artifact,cert

def main():
 p=argparse.ArgumentParser(); p.add_argument('--source',type=Path,required=True); p.add_argument('--out',type=Path,required=True)
 p.add_argument('--hubs',type=int,default=128); p.add_argument('--seed',type=int,default=0); p.add_argument('--rounds',type=int,default=3)
 a=p.parse_args(); raw=a.source.read_bytes(); start=time.monotonic(); artifact,cert=contract(json.loads(raw),a.hubs,a.seed,a.rounds)
 cert['source_sha256']=hashlib.sha256(raw).hexdigest(); write(a.out/'polynomial.json',artifact); write(a.out/'certificate.json',cert); write(a.out/'metrics.json',artifact['metrics'])
 print(json.dumps({'metrics':artifact['metrics'],'contraction':{k:v for k,v in cert['contraction'].items() if k!='root_map'},'seconds':time.monotonic()-start},sort_keys=True),flush=True)
if __name__=='__main__': main()
