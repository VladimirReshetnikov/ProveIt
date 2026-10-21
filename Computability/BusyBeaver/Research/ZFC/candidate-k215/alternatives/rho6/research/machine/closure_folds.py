#!/usr/bin/env python3
"""Use one-row rewrite equivalence classes to propose multirow folds; joint check obligatory."""
from pathlib import Path
from collections import defaultdict,Counter
import importlib.util,itertools,json,sys,time
D=Path(__file__).resolve().parent
sys.path.insert(0,str(D/'folds'))
import filter_source as f,check_joint_fold as c
oldp=Path(sys.argv[1]); rew=Path(sys.argv[2]);out=Path(sys.argv[3]);out.mkdir(parents=True,exist_ok=False)
O,st=c.read(oldp);Q=sorted({q for q,b in O});A={k:{v}for k,v in O.items()}
for h in json.loads(rew.read_text())['hits']:A[tuple(h['row'])].add(tuple(h['new']))
I=c.domain(O,st,7);cache={};stats=Counter();hits=[];tic=time.monotonic()
for keep,drop in itertools.permutations(Q,2):
 phi=lambda z:keep if z==drop else z
 acts=[]
 for b in(0,1):
  left={(w,d,phi(z))for w,d,z in A[keep,b]};right={(w,d,phi(z))for w,d,z in A[drop,b]}
  acts.append(left&right)
 if not all(acts):continue
 N={(q,b):(w,d,phi(z))for(q,b),(w,d,z)in O.items()if q!=drop}
 for a0,a1 in itertools.product(*[sorted(x)for x in acts]):
  N[keep,0]=a0;N[keep,1]=a1;stats['candidates']+=1
  fail=f.local_filter(O,N,I,keep,drop,cache,97,7)
  if fail is not None:stats['rejected']+=1;continue
  hit={'keep':keep,'drop':drop,'actions':[a0,a1]};print('SURVIVOR',hit,flush=True)
  try:proof=c.check(O,N,st,phi(st),keep,drop,7,97)
  except Exception as exc:stats['independent_rejected']+=1;print('FAIL',str(exc));continue
  stats['verified']+=1;hit['proof']=proof;hits.append(hit);tag=f'fold-{keep}-{drop}-{stats["verified"]}';(out/(tag+'.tm')).write_bytes(f.encode(N,phi(st)));(out/(tag+'.json')).write_text(json.dumps(hit,indent=2)+'\n')
r={'status':'COMPLETE_REWRITE_CLOSURE_FOLD_SEARCH','stats':dict(stats),'hits':hits,'seconds':time.monotonic()-tic};(out/'result.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
