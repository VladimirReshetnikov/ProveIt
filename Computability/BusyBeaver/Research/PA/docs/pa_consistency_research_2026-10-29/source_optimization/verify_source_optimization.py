#!/usr/bin/env python3
"""Rebuild and verify a 3904-primitive specialization of the class-A U208 source.

Python standard library only. This is a finite, explicitly checked source
certificate; it is not a smaller literal TM or a proof-assistant theorem.
All checks use explicit exceptions and remain active under python -O.
"""
from pathlib import Path
from collections import deque
import hashlib,json,argparse
HERE=Path(__file__).resolve().parent
EXPECTED_SOURCE_SHA='cddbed7f20e7a8b085b7ca0e76811d07b021522375643b5d1134eec0d2d23164'
SEED_PC=136
SEED=(1,0,13,0,0,1,0,0,1)
REMOVED={3847,3848,3849,3891,3892}

def need(ok,msg):
 if not ok:raise ValueError(msg)

def compact(x):return (json.dumps(x,separators=(',',':'))+'\n').encode('ascii')
def sha(x):return hashlib.sha256(x).hexdigest()
def leaf(n):return isinstance(n[0],str)

def tree(rows):
 d={p:(op,arg) for p,op,arg in rows};need(len(d)==len(rows),'duplicate addresses')
 prefixes={p[:k] for p in d for k in range(len(p))}
 need(not prefixes.intersection(d),'overlapping source leaves')
 need(all(p+b in prefixes or p+b in d for p in prefixes for b in '01'),'not a full tree')
 def rec(p):return d[p] if p in d else (rec(p+'0'),rec(p+'1'))
 result=rec('');need(sites(result)==rows,'noncanonical source order');return result

def sites(n,p=''):
 if leaf(n):return [[p,*n]]
 return sites(n[0],p+'0')+sites(n[1],p+'1')

def subtree(n,p):
 for b in p:need(not leaf(n),'path below leaf');n=n[int(b)]
 return n

def replace(n,p,r):
 if not p:return r
 a=list(n);a[int(p[0])]=replace(a[int(p[0])],p[1:],r);return tuple(a)

def metrics(n):
 seen=set()
 def rec(n):
  if n in seen:return
  seen.add(n)
  if not leaf(n):rec(n[0]);rec(n[1])
 rec(n);rs=sites(n)
 return dict(primitives=len(rs),distinct_subtrees=len(seen),maximum_depth=max(len(p) for p,_,_ in rs),maximum_zero_run=max(len(z) for p,_,_ in rs for z in p.split('1')))

def cfg_intervals(rows):
 intervals={}
 for i,(p,op,arg) in enumerate(rows):
  for k in range(len(p)+1):
   x=p[:k]
   if x not in intervals:intervals[x]=[i,i+1]
   else:intervals[x][1]=i+1
 def jump(p,b,n):
  while p:
   x,p=p[-1],p[:-1]
   if x==b:
    n-=1
    if n==0:return intervals[p][1]%len(rows) if b=='0' else intervals[p][0]
  return 0
 out=[]
 for i,(p,op,arg) in enumerate(rows):
  nxt=(i+1)%len(rows)
  if op=='CI':ts=[nxt]
  elif op=='CD':ts=[jump(p,'0',1),nxt]
  elif op=='CB':ts=[jump(p,'0',arg)]
  elif op=='CC':ts=[jump(p,'1',arg)]
  elif op=='CH':ts=[]
  else:raise ValueError('unknown opcode')
  out.append([op,arg,ts])
 return out

def cfg_binary(rows):
 leaves={p:i for i,(p,_,_) in enumerate(rows)};depth=max(map(len,leaves))
 def locate(prefix):
  word=prefix+'0'*depth
  for k in range(1,depth+1):
   if word[:k] in leaves:
    need('1' not in prefix[k:],'stray successor one');return leaves[word[:k]]
  raise ValueError('missing successor leaf')
 def inc(p):
  if not p:return ''
  return format((int(p,2)+1)%(1<<len(p)),'0'+str(len(p))+'b')
 def cut(p,b,n):
  inds=[k for k,x in enumerate(p) if x==b]
  return p[:inds[-n]] if len(inds)>=n else ''
 out=[]
 for p,op,arg in rows:
  if op=='CI':ts=[locate(inc(p))]
  elif op=='CD':ts=[locate(inc(cut(p,'0',1))),locate(inc(p))]
  elif op=='CB':ts=[locate(inc(cut(p,'0',arg)))]
  elif op=='CC':ts=[locate(cut(p,'1',arg))]
  else:need(op=='CH','unknown opcode');ts=[]
  out.append([op,arg,ts])
 return out

def mask_next(g,i,m):
 op,arg,ts=g[i]
 if op=='CI':return [(ts[0],m|(1<<arg))]
 if op=='CD':
  return [(ts[1],m),(ts[1],m&~(1<<arg))] if m&(1<<arg) else [(ts[0],m)]
 return [(ts[0],m)] if op!='CH' else []

def r1_next(g,i,x):
 op,arg,ts=g[i]
 if op=='CI':return [(ts[0],1 if arg==1 else x)]
 if op=='CD':
  if arg!=1:return [(j,x) for j in ts]
  return [(ts[0],0)] if x==0 else [(ts[1],0),(ts[1],1)]
 return [(ts[0],x)] if op!='CH' else []

def r6_next(g,i,x):
 op,arg,ts=g[i]
 if op=='CI':return [(ts[0],min(2,x+1) if arg==6 else x)]
 if op=='CD':
  if arg!=6:return [(j,x) for j in ts]
  if x==0:return [(ts[0],0)]
  if x==1:return [(ts[1],0)]
  return [(ts[1],1),(ts[1],2)]
 return [(ts[0],x)] if op!='CH' else []

def closure(g,seed,next_states):
 reached=[set() for _ in g];reached[SEED_PC].add(seed);work=deque([(SEED_PC,seed)])
 while work:
  i,x=work.popleft()
  for j,y in next_states(g,i,x):
   if y not in reached[j]:reached[j].add(y);work.append((j,y))
 # Independently verify the returned finite family is inductive.
 need(seed in reached[SEED_PC],'missing abstract initial state')
 for i,xs in enumerate(reached):
  for x in xs:
   for j,y in next_states(g,i,x):need(y in reached[j],'abstract family not closed')
 return reached

def build(output):
 raw=(HERE/'original_sites.json').read_bytes();need(sha(raw)==EXPECTED_SOURCE_SHA,'original source hash mismatch');old=json.loads(raw);ot=tree(old)
 need(len(old)==3909,'wrong original source size')
 og=cfg_intervals(old);need(og==cfg_binary(old),'original resolvers disagree')
 need(subtree(ot,'0011011100')==(('CD',1),(('CI',6),('CC',2))),'first loop identity')
 need(subtree(ot,'1110011')==((('CD',6),('CC',2)),('CB',1)),'target-test identity')
 nt=replace(ot,'001101110',subtree(ot,'0011011101'))
 nt=replace(nt,'1110011',('CB',1));new=sites(nt);ng=cfg_intervals(new)
 need(ng==cfg_binary(new),'new resolvers disagree');need(len(new)==3904,'new source census')
 keep=[i for i in range(len(old)) if i not in REMOVED];rename={i:j for j,i in enumerate(keep)}
 def project(i):
  if i==3847:i=3850
  if i==3891:i=3893
  need(i in rename,'edge enters a removed nonidentity instruction');return rename[i]
 for old_i,new_i in rename.items():
  need(old[old_i][1:]==new[new_i][1:],'changed surviving primitive')
  need(ng[new_i][2]==[project(j) for j in og[old_i][2]],'source edge projection failed')
 need(old[SEED_PC]==new[SEED_PC],'startup source leaf changed')
 seedmask=sum(1<<i for i,v in enumerate(SEED) if v)
 masks=closure(og,seedmask,mask_next)
 need(all(not(m&(1<<1)) for m in masks[3847]),'register1 need not be zero at3847')
 need(not masks[3848] and not masks[3849],'first loop body reachable')
 r1=closure(og,0,r1_next)
 need(r1[3847]=={0} and not r1[3848] and not r1[3849],'single-register first-loop invariant failed')
 r6=closure(og,0,r6_next)
 need(r6[3891]=={0} and not r6[3892],'target-test decrement not proved zero')
 need(og[3847][2][0]==3850 and og[3891][2][0]==3893,'wrong identity exits')
 output=Path(output);output.mkdir(parents=True,exist_ok=True)
 (output/'optimized_sites.json').write_bytes(compact(new))
 (output/'optimized_cfg.json').write_bytes(compact(ng))
 # A 512-bit invariant mask for each source ordinal, little endian.
 certificate=b''.join(sum(1<<m for m in xs).to_bytes(64,'little') for xs in masks)
 (output/'zero_positive_invariant.bin').write_bytes(certificate)
 (output/'register1_zero_positive_invariant.json').write_bytes(compact([sorted(xs) for xs in r1]))
 (output/'register6_trit_invariant.json').write_bytes(compact([sorted(xs) for xs in r6]))
 ledger={'removed_old_ordinals':sorted(REMOVED),'retained_old_ordinals':keep,
         'identity_old_steps':{'3847':3850,'3891':3893},'unreachable_old_ordinals':[3848,3849,3892],
         'old_to_new':rename,'initial_ordinal':SEED_PC,'initial_registers':SEED}
 (output/'source_projection.json').write_text(json.dumps(ledger,indent=2)+'\n')
 incoming={i:[] for i in range(len(old))}
 for i,(op,arg,ts) in enumerate(og):
  for k,j in enumerate(ts):incoming[j].append({'ordinal':i,'branch':('zero' if k==0 else 'positive') if op=='CD' else 'unconditional'})
 inventory={'register1_region':{i:incoming[i] for i in range(3837,3850)},
            'register6_region':{i:incoming[i] for i in range(3883,3895)}}
 (output/'incoming_regions.json').write_text(json.dumps(inventory,indent=2)+'\n')
 result={'status':'SOURCE_OPTIMIZATION_PASS','old_metrics':metrics(ot),'new_metrics':metrics(nt),
  'old_edges':sum(len(r[2]) for r in og),'new_edges':sum(len(r[2]) for r in ng),
  'zero_positive_abstract_pairs':sum(map(len,masks)),'register1_abstract_pairs':sum(map(len,r1)),'register6_abstract_pairs':sum(map(len,r6)),
  'mask_set_at_3847':sorted(masks[3847]),'register6_categories_at_3891':sorted(r6[3891]),
  'original_sites_sha256':sha(raw),'optimized_sites_sha256':sha(compact(new)),
  'zero_positive_invariant_sha256':sha(certificate),
  'claim':'Halting equivalence of the two source programs from the stated canonical seed, by the checked inductive invariants and source-step projection.',
  'literal_tm_states':None,'literal_tm_warning':'No literal table implementing the optimized source is supplied; no state saving follows from this source count.'}
 (output/'result.json').write_text(json.dumps(result,indent=2)+'\n');return result
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--output',type=Path,default=HERE/'generated');a=p.parse_args()
 print(json.dumps(build(a.output),indent=2))
