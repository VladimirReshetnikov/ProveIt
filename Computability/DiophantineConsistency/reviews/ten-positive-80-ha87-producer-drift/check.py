#!/usr/bin/env python3
"""Compare byte-identical HA87 author records to the 80 selected closure."""
from collections import defaultdict,deque
from hashlib import sha256
from pathlib import Path
import json
H=Path(__file__).resolve().parent;D=H.parents[1]
SCAN=D/'reviews/ten-positive-80-fixed-ipra-serialized-closure/observations/attempt01/result.json'
EXTRA=D/'reviews/ten-positive-80-adaptive-producer-drift/observations/attempt01.json'
BASE=D/'research/ordinary12-direct90-ipra-join/observations/attempt03/result.json'
STATE=D/'reviews/ha87-isolated-full-author-pass/state.json';OUT=H/'observations/attempt01.json'
NAMES={'DiophantineConsistency.'+n for n in ('ArithmeticNegativeNorms','ArithmeticCarrierSoundness2011','ArithmeticCarrierRadix2011','ArithmeticWindowInterface')}
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(not OUT.exists(),'output exists')
x=json.loads(SCAN.read_text());extra=json.loads(EXTRA.read_text());b=json.loads(BASE.read_text());state=json.loads(STATE.read_text())
need(state['status']=='PASS' and x['status']=='PASS','input status')
records={};drifts=[]
for r in state['records']:
 n=r.get('module')
 if n not in NAMES:continue
 chosen=x['project'][n]['selected'];need(r['verified'] and r['exit']==0 and r['object_sha256']==chosen['sha256']==sha(chosen['path']),'object mismatch '+n)
 source=next((Path(p) for p in r['command'] if p.endswith('.lean')),None)
 source_info={'path':str(source),'recorded_sha256':r['source_sha256'],
              'current_sha256':sha(source) if source and source.is_file() else None}
 deps={}
 for dep,h in r['dependency_hashes'].items():
  final=x['project'].get(dep,{}).get('selected',x['outside'].get(dep));need(final is not None,'missing dependency '+n+' '+dep)
  z={'recorded_sha256':h,'final_selected':final,'matches':h==final['sha256']};deps[dep]=z
  if not z['matches']:drifts.append({'module':n,'dependency':dep,**z})
 records[n]={'selected':chosen,'historical_record':r,'historical_source':source_info,'direct_compared':deps}
need(set(records)==NAMES and len(drifts)==11,'unexpected records/drifts')
prior=b['post_headers']['project'];graph={n:r['imports'] for n,r in prior.items() if n in x['project']};graph.update(x['fresh_headers']);rev=defaultdict(set)
for n,ds in graph.items():
 for dep in ds:rev[dep].add(n)
seeds=set(extra['combined_seeds'])|{z['module'] for z in drifts};affected=set(seeds);q=deque(seeds)
while q:
 for n in rev[q.popleft()]:
  if n not in affected:affected.add(n);q.append(n)
need(len(affected)==127 and not affected&set(prior),'unexpected cone')
out={'status':'COMPARED_WITH_DRIFTS','inputs':{str(p):sha(p) for p in (SCAN,EXTRA,BASE,STATE)},
     'author_search_path':state['LEAN_PATH'],'records':records,'drifts':drifts,
     'combined_seeds':sorted(seeds),'affected':sorted(affected),
     'scope':'byte-identical historical author-state outputs and recorded dependency hashes; recorded names do not authenticate unique selected producer or full project/package/dynamic ancestry'}
OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':out['status'],'matched':len(records),'drifts':len(drifts),'affected':len(affected),'sha256':sha(OUT)},sort_keys=True))
