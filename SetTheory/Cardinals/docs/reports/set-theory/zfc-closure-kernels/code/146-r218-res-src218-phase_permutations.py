#!/usr/bin/env python3
"""All24 orders of four closed phases; logical calibration is tracked separately.

Only cyclic orders ABCD/ACBD preserve the ordinary command parser up to a
swap of its first two fields. Other orders are explicitly uncalibrated.
"""
from pathlib import Path
from itertools import permutations
import hashlib,json,subprocess,sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'source_work'));import rotation_search as r
OUT=ROOT/'source218/phase_permutations';OUT.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def rebuild(xs):return xs[0]if len(xs)==1 else(xs[0],rebuild(xs[1:]))
standard={tuple(v[k:]+v[:k])for v in([0,1,2,3],[0,2,1,3])for k in range(4)}
orders=sorted(permutations(range(4)),key=lambda p:(p not in standard,p))
results=[]
for label,tablepath,sourcepath in [
 ('published',ROOT/'baseline219/K219_Construction_2026-10-20/machine/k219.native.tm',ROOT/'baseline219/K219_Construction_2026-10-20/machine/sites219.json'),
 ('alternative',ROOT/'source218/alternative219/candidate.tm',ROOT/'source218/alternative219/sites.json')]:
 T=r.b.read_table(tablepath.read_bytes());oldrows=json.loads(sourcepath.read_text());old=r.s.tree(oldrows)
 phases=[r.s.subtree(old,p)for p in('0','10','110','111')]
 assert rebuild(phases)==old and all(r.s.boundary(x)[:2]==(0,0)for x in phases)
 starts=[0]
 for x in phases:starts.append(starts[-1]+len(r.s.sites(x)))
 phaseq=[];outerq=[];q=84
 for i in range(3):
  outerq.append(q);aa,bb=T[q,0],T[q,1]
  assert aa[:2]==(0,1)and bb[:2]==(1,1)
  phaseq.append(aa[2]);q=bb[2]
 phaseq.append(q);og=r.s.graph_arithmetic(oldrows)[0];assert og==r.s.graph_intervals(oldrows)
 for order in orders:
  new=rebuild([phases[i]for i in order]);rows=r.s.sites(new);ng=r.s.graph_arithmetic(rows)[0]
  assert ng==r.s.graph_intervals(rows)
  newstart={};p=0
  for i in order:newstart[i]=p;p+=starts[i+1]-starts[i]
  expected=[]
  for i in order:
   for j in range(starts[i],starts[i+1]):
    effect,targets=og[j];nt=[]
    for target in targets:
     if starts[i]<=target<starts[i+1]:nt.append(newstart[i]+target-starts[i])
     else:
      assert target==starts[i+1]%len(rows),(i,j,target)
      nt.append((newstart[i]+starts[i+1]-starts[i])%len(rows))
    expected.append([effect,nt])
  assert ng==expected
  U=dict(T)
  for i,q in enumerate(outerq):
   U[q,0]=(0,1,phaseq[order[i]])
   U[q,1]=(1,1,outerq[i+1]if i<2 else phaseq[order[3]])
  name=''.join('ABCD'[i]for i in order);folder=OUT/f'{label}_{name}';folder.mkdir(exist_ok=True)
  (folder/'sites.json').write_bytes(r.s.compact(rows))
  for count in(219,218):
   V=dict(U)
   if count==218:
    V={(q,b):(w,d,88 if z==301 else z)for(q,b),(w,d,z)in V.items()if q!=301}
    V[88,0]=(0,-1,51);V[88,1]=(1,1,103);V[51,0]=(0,1,122);V[51,1]=(1,1,51)
   (folder/f'phase{count}.tm').write_bytes(r.b.table_bytes(V))
   with(folder/f'start{count}.txt').open('w')as of,(folder/f'start{count}.log').open('w')as ef:
    subprocess.run([str(ROOT/'source218/alternative301_search/search_start_weak'),str(folder/f'phase{count}.tm'),'3000000'],stdout=of,stderr=ef,check=True)
   lines=(folder/f'start{count}.txt').read_text().splitlines()
   rec={'layout':label,'order':name,'state_count':count,'source_metrics':r.s.metrics(new),
        'source_sha256':sha(folder/'sites.json'),'table_sha256':sha(folder/f'phase{count}.tm'),
        'exact_closed_phase_cfg_check':True,'command_calibration':'ORDINARY_OR_FIELD_SWAP'if order in standard else'UNPROVED',
        'startup_hits':len(lines),'startup_output':lines,'folder':str(folder.relative_to(ROOT))}
   results.append(rec);(folder/f'receipt{count}.json').write_text(json.dumps(rec,indent=2)+'\n')
   print(json.dumps({k:v for k,v in rec.items()if k!='startup_output'}),flush=True)
   (OUT/'summary.json').write_text(json.dumps({'status':'RUNNING','results':results},indent=2)+'\n')
(OUT/'summary.json').write_text(json.dumps({'status':'COMPLETED','results':results},indent=2)+'\n')
