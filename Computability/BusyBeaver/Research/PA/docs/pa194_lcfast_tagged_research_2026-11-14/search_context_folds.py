#!/usr/bin/env python3
from pathlib import Path
import sys,json,collections,itertools
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'construction/vendor'))
import compiler as c,support as s
out=[]
for folder in sorted((ROOT/'machines').iterdir()):
 rows=s.read_table(folder/'machine.native.tm')
 incoming=collections.defaultdict(list)
 for (q,b),(w,d,n)in rows.items():incoming[n].append((q,b,w,d))
 shapes={q:None for q in incoming if q!=74 and q!=254 and all(b==w and d for p,b,w,d in incoming[q])}
 ops=c.opportunities_fast(rows,shapes)
 accepted=[]
 for a,b,actions in ops:
  for ac in itertools.product(*actions):
   folds=[[a,b,ac]]
   try:
    child,aliases=s.apply_folds(rows,folds)
    certificate=s.check_local_folds(rows,child,aliases,folds)
   except (AssertionError,KeyError):continue
   accepted.append([a,b,ac]);print('CANDIDATE',folder.name,a,b,ac,flush=True)
   (folder/'candidate193.native.tm').write_text(s.table_text(child))
 result={'family':folder.name,'homogeneous_history_candidates':len(shapes),'pairs':len(ops),'accepted':accepted}
 out.append(result)
 print(json.dumps(result),flush=True)
(ROOT/'context_fold_search.json').write_text(json.dumps(out,indent=2)+'\n')
