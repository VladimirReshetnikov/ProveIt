#!/usr/bin/env python3
"""Compare byte-matching independently verified adaptive producer records."""
from collections import defaultdict,deque
from hashlib import sha256
from pathlib import Path
import json
H=Path(__file__).resolve().parent;D=H.parents[1]
SCAN=D/'reviews/ten-positive-80-fixed-ipra-serialized-closure/observations/attempt01/result.json'
SINGLE=D/'reviews/ten-positive-80-fixed-ipra-serialized-closure/observations/producer-audit01.json'
NINE=D/'reviews/ten-positive-80-nine-prefix-producer-audit/observations/attempt01.json'
BASE=D/'research/ordinary12-direct90-ipra-join/observations/attempt03/result.json'
PEER=D/'reviews/ipra-adaptive-native-fixed-continuation-verification-peer'
STATE=PEER/'author-state.json';RECEIPT=PEER/'receipt.json';OUT=H/'observations/attempt01.json'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(not OUT.exists(),'output exists')
x=json.loads(SCAN.read_text());u=set(json.loads(SINGLE.read_text())['unmatched']);a=json.loads(STATE.read_text());v=json.loads(RECEIPT.read_text());old=json.loads(NINE.read_text());b=json.loads(BASE.read_text())
need(a['status']=='PASS' and v['status']=='MATCHED_PASS' and v['author_state_sha256']==sha(STATE),'historical receipt invalid')
peer={r['name']:r for r in v['matched_rows']};matched={};drifts=[]
for r in a['records']:
 n=r.get('name');selected=x['project'].get(n,{}).get('selected')
 if n not in u or not selected or selected['sha256']!=r['object_sha256']:continue
 need(n in peer and peer[n]['object_sha256']==r['object_sha256'] and r['exit']==0,'peer mismatch '+n)
 deps={}
 for dep,rec in r.get('direct_imports',{}).items():
  final=x['project'].get(dep,{}).get('selected',x['outside'].get(dep))
  need(final is not None,'unresolved final dependency '+n+' '+dep)
  z={'recorded':rec,'final_selected':final,'matches':rec['sha256']==final['sha256']};deps[dep]=z
  if not z['matches']:drifts.append({'module':n,'dependency':dep,**z})
 matched[n]={'historical_record':r,'peer_record':peer[n],'selected':selected,'direct_compared':deps}
need(len(matched)==13 and len(drifts)==2,'unexpected count')
prior=b['post_headers']['project'];graph={n:r['imports'] for n,r in prior.items() if n in x['project']};graph.update(x['fresh_headers']);reverse=defaultdict(set)
for n,ds in graph.items():
 for dep in ds:reverse[dep].add(n)
seeds={z['module'] for z in old['drifts']}|{z['module'] for z in drifts};affected=set(seeds);q=deque(seeds)
while q:
 for n in reverse[q.popleft()]:
  if n not in affected:affected.add(n);q.append(n)
need(len(affected)==122 and not affected&set(prior),'unexpected affected cone')
result={'status':'COMPARED_WITH_DRIFTS','inputs':{str(p):sha(p) for p in (SCAN,SINGLE,NINE,BASE,STATE,RECEIPT)},
        'matched':matched,'drifts':drifts,'combined_seeds':sorted(seeds),'affected':sorted(affected),
        'scope':'byte-identical historical peer-matched outputs and their recorded direct project inputs; uniqueness of actual selected producer and full historical transitive/package/dynamic provenance not established'}
OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':result['status'],'matched':len(matched),'drifts':len(drifts),'affected':len(affected),'sha256':sha(OUT)},sort_keys=True))
