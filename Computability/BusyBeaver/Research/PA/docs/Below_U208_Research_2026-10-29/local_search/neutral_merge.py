from pathlib import Path
from history_search import read
import json,itertools
p=Path(__file__).parent; r=json.loads((p/'neutral.json').read_text());t=read(r['input']);Q=sorted({q for q,b in t}); opts={(q,b):{t[q,b]:set()}for q,b in t}
for e in r['rewrites']:
 q,b,w,d,z=e['row'];deps={step[0]for cs in e['cert']for branch in cs['cases']for step in branch['trace'][1:]};opts[q,b][w,d,z]=deps
out=[]
for q,r in itertools.combinations(Q,2):
 if 0 in(q,r):continue
 o=[]
 for b in(0,1):
  acts=[a for a in opts[q,b].keys()&opts[r,b].keys()if not ({q,r}&(opts[q,b][a]|opts[r,b][a]))]
  if not acts:break
  o.append(acts)
 else:out.append({'q':q,'r':r,'opts':o});print(out[-1])
(p/'neutral_merge.json').write_text(json.dumps(out,indent=2));print('TOTAL',len(out))
