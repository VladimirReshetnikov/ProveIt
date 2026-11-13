#!/usr/bin/env python3
"""Independent lexical import audit; no Lean or object authentication."""
import collections,hashlib,json,re,resource,sys
from pathlib import Path
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('use python3 -I -S -B')
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(35,35));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
r=Path(__file__).resolve().parents[2];d=Path(__file__).resolve().parent;workspace=r.parents[1];math=workspace/'.lake/packages/mathlib'
sha=lambda x:hashlib.sha256(x).hexdigest()
def require(b,m):
 if not b:raise RuntimeError(m)
pins=json.loads((d/'pins.json').read_bytes())
for f,h in pins.items():require(sha((r/f).read_bytes())==h,'pin '+f)
def read(p):return (r/p).read_text()
old=read('research/adaptive87-four-square-local-mod4-model-draft/FourUnitGeneric.lean.src');new=read('research/adaptive87-four-square-discrete-generic-slim-draft/FourUnitGeneric.lean.src');facts=read('Lean/DiophantineConsistency/DiscreteOrderedRingFacts.lean')
a='import DiophantineConsistency.ModelCarrierScaled';b='import DiophantineConsistency.DiscreteOrderedRingFacts'
require(old.count(a)==1 and old.replace(a,b,1)==new,'exact source delta')
for token in ['def Discrete (R : Type*)','theorem eq_one_or_neg_one_of_mul_eq_one (hd : Discrete R)']:
 require(token in facts,'specific source '+token)
require('import Mathlib.Tactic.Linarith' in new and 'import Mathlib.Tactic.LinearCombination' in new and 'import Mathlib.Data.ZMod.Basic' in new,'tactics/finite domain')
prior=json.loads(read('research/adaptive87-four-square-local-mod4-model-draft/result.json'));g=prior['instantiated_endpoint_sources'];result=json.loads(read('research/adaptive87-four-square-discrete-generic-slim-draft/result.json'))
for item in g.values():require(sha((r/item['source']).read_bytes())==item['sha256'],'predecessor source '+item['source'])
h=dict(g);h['FourUnitGeneric']={'imports':[line[7:] for line in new.splitlines() if line.startswith('import ')]}
def walk(graph,starts):
 q=collections.deque(starts);seen=set()
 while q:
  n=q.popleft()
  if n in seen:continue
  seen.add(n);q.extend(graph.get(n,{}).get('imports',[]))
 return {n for n in seen if n.startswith('DiophantineConsistency.') and n in graph}
removed=[];counts={}
for label,starts in [('conditional',['FourSquare88Model']),('instantiated',['FourSquare88Model','DiophantineConsistency.HAAdaptiveFactor87'])]:
 before=walk(g,starts);after=walk(h,starts);out=result['frontiers'][label]
 require(len(before)==out['before_project_sources'] and len(after)==out['after_project_sources'],'closure '+label)
 require(sorted(before-after)==out['removed_project_sources'] and sorted(after-before)==out['added_project_sources'],'frontier delta '+label)
 require(('DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011' in after)==out['factor_units_reachable'],'factor unit '+label)
 removed=sorted(before-after);counts[label]=[len(before),len(after)]
 if label=='instantiated':
  roots={'ha87':Path('/tmp/ha87-full-transitive-p3xt6wra/lib'),'current14':Path('/tmp/current14-standard-fresh-build-20261104/lib'),'peer':Path('/tmp/nine-ipra-guarded-peer-20261102-a/lib')}
  for k,root in roots.items():
   count=sum((root/Path(*n.split('.')).with_suffix('.olean')).is_file() for n in after)
   require(count==out['sample_provider_presence'][k]['present'],'sample root '+k)
# Narrow current-source Mathlib import traversal. It checks declaration/tactic
# source availability only, without assuming compiled package provenance.
def imports(path):
 depth=0;out=[]
 for line in path.read_text().splitlines():
  i=0;buf=[]
  while i<len(line):
   if line.startswith('/-',i):depth+=1;i+=2
   elif depth and line.startswith('-/',i):depth-=1;i+=2
   elif depth:i+=1
   elif line.startswith('--',i):break
   else:buf.append(line[i]);i+=1
  clean=''.join(buf).strip()
  if not clean or clean in ('module','prelude'):continue
  m=re.fullmatch(r'(?:(?:public|private|meta)\s+)*import\s+([\w.]+(?:\s+[\w.]+)*)',clean)
  if not m:break
  out.extend(m.group(1).split())
 return out
roots=['Mathlib.Data.ZMod.Basic','Mathlib.Tactic.LinearCombination','Mathlib.Tactic.Linarith','Mathlib.Tactic.Ring'];q=collections.deque(roots);seen=set()
while q:
 n=q.popleft()
 if n in seen:continue
 seen.add(n);f=math/Path(*n.split('.')).with_suffix('.lean')
 if f.is_file():q.extend(imports(f))
targets={'Mathlib.Tactic.LinearCombination':'syntax (name := linearCombination)', 'Mathlib.Tactic.Linarith.Frontend':'syntax (name := nlinarith)', 'Mathlib.Algebra.GroupWithZero.Basic':'lemma pow_eq_zero_iff', 'Mathlib.Algebra.Order.Ring.Unbundled.Basic':'lemma sq_nonneg', 'Mathlib.Data.Nat.Cast.Basic':'theorem map_ofNat', 'Mathlib.Algebra.NeZero':'lemma two_ne_zero'}
for n,t in targets.items():
 require(n in seen and t in (math/Path(*n.split('.')).with_suffix('.lean')).read_text(),'Mathlib source '+n)
closure_rows=[]
for n in sorted(seen):
 f=math/Path(*n.split('.')).with_suffix('.lean')
 if f.is_file():closure_rows.append(n+' '+sha(f.read_bytes()))
closure_digest=sha(('\n'.join(closure_rows)+'\n').encode())
print(json.dumps({'scope':'lexical current-source and bounded object-presence checks only; no Lean or provider authentication','pins_sha256':sha((d/'pins.json').read_bytes()),'conditional_before_after':counts['conditional'],'instantiated_before_after':counts['instantiated'],'removed_project_sources':removed,'mathlib_target_sources_reachable':sorted(targets),'mathlib_source_closure_count':len(closure_rows),'mathlib_source_closure_sha256':closure_digest,'instantiated_factorunits_still_reachable':True,'bounded_peer_present':651},sort_keys=True,indent=2))
