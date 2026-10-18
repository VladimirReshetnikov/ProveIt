"""Explicit source pins and freshly derived two-way finite bisimulation.
Only data from the chosen named source bundle enters calibration.
"""
from pathlib import Path
import json,hashlib
from functools import lru_cache
P=Path(__file__).resolve().parent
SOURCE_PINS={
 'original254':('1e989801225be6a66477fe6c4f7dcc7c08751fc1c03cc65c321a08e8528625b0',6460),
 'dne32':('082911b3cc8d36a0c6135a7b17fd246b8792d10bf4376d0ba4531f6285b3bd29',6366),
}
def load_bundle(name):
 b=json.loads((P/'pinned_source_bundles.json').read_text())[name]
 assert (b['source_sites_sha256'],b['leaf_count'])==SOURCE_PINS[name]
 return dict(b,bundle_id=name)
def load_source_sites(b):
 raw=(P/b['source_sites']).read_bytes()
 assert hashlib.sha256(raw).hexdigest()==b['source_sites_sha256']
 sites=json.loads(raw);assert len(sites)==b['leaf_count']
 return sites

def prove_bisimulation(source,candidate):
 """Same guarded effects in finite normalized segments proves both halting directions.
 Each pure-control/increment segment terminates by a checked acyclic pointer trace.
 Determinism then relates all natural register vectors by guarded induction.
 """
 maps=[{p:(op,arg) for p,op,arg in ss} for ss in (source,candidate)]
 depths=[max(map(len,m)) for m in maps]
 def inc(p):
  return format((int(p or '0',2)+1)%(1<<len(p)),'0'+str(len(p))+'b') if p else ''
 def cut(p,b,n):
  for _ in range(n):
   i=p.rfind(b)
   if i<0:return ''
   p=p[:i]
  return p
 @lru_cache(None)
 def decode(k,p):
  ex=p+'0'*depths[k]
  for d in range(1,depths[k]+1):
   leaf=ex[:d]
   if leaf in maps[k]:return maps[k][leaf],leaf
  raise AssertionError(('Incomplete source tree',k,p))
 @lru_cache(None)
 def segment(k,p):
  effects=[0]*9;seen=set();count=0
  while True:
   assert p not in seen,('Nonterminating pure segment',k,p)
   seen.add(p);(op,arg),leaf=decode(k,p)
   if op in ('CD','CH'):return tuple(effects),p,count
   count+=1
   if op=='CI':effects[arg]+=1;p=inc(leaf)
   elif op=='CB':p=inc(cut(leaf,'0',arg))
   elif op=='CC':p=cut(leaf,'1',arg)
   else:raise AssertionError((op,arg))
 ea,pa,na=segment(0,'');eb,pb,nb=segment(1,'')
 assert ea==eb
 initial_effects=ea
 queue=[(pa,pb)];seen={(pa,pb)};edges=halts=0;max_segment=max(na,nb)
 for pa,pb in queue:
  (oa,aa),la=decode(0,pa);(ob,ab),lb=decode(1,pb)
  assert (oa,aa)==(ob,ab),('Guarded operation mismatch',pa,pb,(oa,aa),(ob,ab))
  if oa=='CH':halts+=1;continue
  assert oa=='CD'
  for zero in (False,True):
   a=inc(cut(la,'0',1)) if zero else inc(la)
   b=inc(cut(lb,'0',1)) if zero else inc(lb)
   ea,qa,na=segment(0,a);eb,qb,nb=segment(1,b)
   assert ea==eb,('Unequal between-guard increments',qa,qb,ea,eb)
   max_segment=max(max_segment,na,nb);pair=(qa,qb)
   if pair not in seen:seen.add(pair);queue.append(pair)
   edges+=1
 assert halts>0
 return {'status':'TWO_WAY_REGISTER_BISIMULATION_PASS','reachable_guarded_pairs':len(queue),'checked_guard_edges':edges,'halt_pairs':halts,'maximum_pure_segment_instructions':max_segment,'initial_increment_effects':initial_effects,'both_halting_directions':True,'all_natural_register_vectors':True,'proof_method':'Finite closed guarded relation, equal terminating pure-segment effects, same decrement register and both guards, same halt outcome; mathematical induction on guarded execution'}
