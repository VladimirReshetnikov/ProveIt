"""Reproducible independent-cube and per-prefix minimality audit."""
import json,random,sys,time,platform
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'src'))
from graded_scan import scan,Limits
from graded_cube import cube
from block_plan import plan,verify
from reference_cube import cube_homology

def run():
 rng=random.Random(20261008); cases=[]
 for i in range(160):
  s=rng.randint(2,5); n=rng.randint(0,9)
  w=[rng.choice((-1,1))*rng.randrange(1,s) for _ in range(n)]
  cases.append((s,w))
 for m in range(1,4):
  for pat in ([1,2,3],[3,2,1],[-1,-2,-3],[-3,-2,-1]): cases.append((4,pat*m))
 cases.extend([(4,[1,2,3]*2+[-2,1]),(5,[2,3,4]*2+[1]),(4,[1,-2,3]*3)])
 rows=[]; prefix_checks=entry_checks=0; start=time.perf_counter()
 for idx,(s,w) in enumerate(cases):
  independent=cube(s,w)
  modes=('local','reverse','reference','rebuild') if idx<60 else ('local',)
  previous=None
  for mode in modes:
   r=scan(s,w,reducer=mode,audit=True,record_profiles=True,limits=Limits(seconds=40))
   assert r['bigraded_homology']==independent['bigraded_homology'],(idx,s,w,mode)
   profiles=[t['profile'] for t in r['trace']]
   if previous is not None: assert previous==profiles,(idx,'graded prefix mismatch')
   previous=profiles; entry_checks+=r['checked_entries']; prefix_checks+=len(w)
   if mode in ('local','reverse','rebuild'):
    for t in r['trace']:
     assert t['max_incidence']<=(2*s+1)*t['pre_occupancy']
     assert t['queue_pushes']<=t['pre_entries']+t['update_pairs']
  if idx<60:
   prior=cube_homology(s,w)
   by_h={}
   for h,q,b in independent['bigraded_homology']: by_h[h]=by_h.get(h,0)+b
   assert by_h=={h:2*b for h,b in prior['by_degree'].items()}
  certificates=plan(s,w)
  for p in certificates: assert verify(s,w,p['pieces'])==(p['blocks'],p['defects'])
  rows.append(dict(strands=s,word=w,bigraded_homology=independent['bigraded_homology'],
                   cube_basis=independent['basis'],reducers=list(modes)))
  if idx%25==0: print('validated',idx,flush=True)
 result=dict(seed=20261008,python=sys.version,platform=platform.platform(),cases=len(cases),
             scans=sum(len(x['reducers']) for x in rows),prefix_checks=prefix_checks,
             entry_checks=entry_checks,prior_cube_checks=60,failures=0,
             seconds=time.perf_counter()-start,results=rows)
 (ROOT/'results'/'validation.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v for k,v in result.items() if k!='results'},indent=2))
if __name__=='__main__': run()
