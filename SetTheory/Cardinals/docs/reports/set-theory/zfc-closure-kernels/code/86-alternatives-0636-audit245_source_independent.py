#!/usr/bin/env python3
"""Check supplied RM bisimulation independently of rmpath and its producer."""
if not __debug__:raise RuntimeError('Assertions required')
from pathlib import Path
import importlib.util,sys,json,hashlib
V=Path(__file__).resolve().parent;A=V.parent/'audit245/extracted/zfc245-proof-20261018';B=V/'baseline246_rerun'
sp=importlib.util.spec_from_file_location('reviewed_baseline_source_parser',B/'code/review_affine_source.py');parser=importlib.util.module_from_spec(sp);sp.loader.exec_module(parser)
_,old=parser.parse_source(A/'reference/context246/sources/Prog254.v')
new=json.loads((A/'certificate/sites_logical.json').read_text());phys=parser.PHYSICAL;inv={p:i for i,p in enumerate(phys)}
old=[[p,op,inv[r]if op in('CI','CD')else r]for p,op,r in old]
assert [(o,r)for p,o,r in old]==[(o,r)for p,o,r in new]

def tree(rows):
 leaves={p:(o,r)for p,o,r in rows};assert len(leaves)==6460
 prefixes={p[:i]for p in leaves for i in range(len(p))}
 assert not prefixes&set(leaves) and len(prefixes)==6459
 assert all(p+b in prefixes or p+b in leaves for p in prefixes for b in '01')
 return leaves,max(map(len,leaves))

def site(t,p):
 leaves,depth=t;q=''
 for i in range(depth):
  q+=p[i]if i<len(p)else'0'
  if q in leaves:
   assert set(p[len(q):])<={'0'},('unclean residual',p,q)
   return leaves[q],q
 raise AssertionError('unterminated tree')

def inc(p):
 n=len(p);return format((int(p,2)+1)%(2**n),f'0{n}b')if n else''
def strip(p,b,k):
 positions=[i for i,x in enumerate(p)if x==b]
 return p if k==0 else p[:positions[-k]]if len(positions)>=k else''
def segment(t,p):
 counts=[0]*9;seen=set();steps=0
 while True:
  assert p not in seen,('nonterminating control segment',p);seen.add(p)
  (op,r),q=site(t,p)
  if op in('CD','CH'):return tuple(counts),p,steps
  if op=='CI':counts[r]+=1;p=inc(q)
  elif op=='CB':p=inc(strip(q,'0',r))
  else:assert op=='CC';p=strip(q,'1',r)
  steps+=1

ot,nt=tree(old),tree(new);cert=json.loads((A/'certificate/register_bisimulation.json').read_text());E=cert['entries'];assert cert['start_pair']==0 and len(E)==3013
co,po,so=segment(ot,'');cn,pn,sn=segment(nt,'');assert co==cn and E[0][:2]==[po,pn]
edges=halts=0;maxsegment=max(so,sn);reachable={0};todo=[0]
while todo:
 i=todo.pop();pa,pb,nz,z=E[i];a,qa=site(ot,pa);b,qb=site(nt,pb);assert a==b
 if a[0]=='CH':assert nz is None and z is None;halts+=1;continue
 assert a[0]=='CD'
 for dest,ap,bp in [(nz,inc(qa),inc(qb)),(z,inc(strip(qa,'0',1)),inc(strip(qb,'0',1)))]:
  assert type(dest)is int and 0<=dest<len(E)
  ca,sa,ka=segment(ot,ap);cb,sb,kb=segment(nt,bp);assert ca==cb and E[dest][:2]==[sa,sb]
  maxsegment=max(maxsegment,ka,kb);edges+=1
  if dest not in reachable:reachable.add(dest);todo.append(dest)
assert len(reachable)==3013 and edges==6024 and halts==1
identities={}
for r in ['code/check_macro_inductions.py','code/review_affine_source.py','sources/prior/prefix_affine.py','sources/Prog254.v','reviews/independent-calibration.tex']:
 identities[r]=(A/'reference/context246'/r).read_bytes()==(B/r).read_bytes();assert identities[r]
seed=V.parent/'source/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/LogicalSeed246.lean'
assert seed.read_bytes()==(A/'reference/current/LogicalSeed246.lean').read_bytes()
out={'status':'PASS','source_leaves':6460,'ordered_operations_identical':True,'reachable_bisimulation_pairs':3013,'both_guard_edges':6024,'halt_pairs':1,'largest_control_increment_segment':maxsegment,'all_residual_paths_clean':True,'reviewed_baseline_byte_identities':identities,'logical_seed_module_identical_to_pin7ba':True,'new_sites_sha256':hashlib.sha256((A/'certificate/sites_logical.json').read_bytes()).hexdigest(),'certificate_sha256':hashlib.sha256((A/'certificate/register_bisimulation.json').read_bytes()).hexdigest(),'scope':'All-natural-register bisimulation; finite segments aggregated by commuting increments, with every decrement guard and halt preserved.'}
(V/'audit245_source_independent.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
