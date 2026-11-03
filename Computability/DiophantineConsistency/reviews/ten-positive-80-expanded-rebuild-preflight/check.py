#!/usr/bin/env python3
"""Build a pinned source/import plan for the expanded 122-module cone."""
from collections import defaultdict,deque
from hashlib import sha256
from pathlib import Path
import json
H=Path(__file__).resolve().parent;D=H.parents[1]
SCAN=D/'reviews/ten-positive-80-fixed-ipra-serialized-closure/observations/attempt01/result.json'
OLD=D/'reviews/ten-positive-80-rebuild-source-preflight/observations/attempt01.json'
EXTRA=D/'reviews/ten-positive-80-adaptive-producer-drift/observations/attempt01.json'
MAN=D/'reviews/ipra-adaptive-native-fixed-continuation/manifest.json'
PEER=D/'reviews/ipra-adaptive-native-fixed-continuation-verification-peer/receipt.json'
SINGLE=D/'reviews/ten-positive-80-fixed-ipra-serialized-closure/observations/producer-audit01.json'
OUT=H/'observations/attempt01.json'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(not OUT.exists(),'output exists')
x=json.loads(SCAN.read_text());old=json.loads(OLD.read_text());ext=json.loads(EXTRA.read_text());man=json.loads(MAN.read_text());peer=json.loads(PEER.read_text());single=json.loads(SINGLE.read_text())
need(sha(MAN)==peer['manifest_sha256'] and peer['status']=='MATCHED_PASS','manifest/peer mismatch')
affected=set(ext['affected']);need(len(affected)==122 and set(old['ordered'])<=affected,'unexpected cone')
graph={n:x['fresh_headers'][n] for n in affected}; reverse=defaultdict(set)
for n,deps in graph.items():
 for dep in deps:reverse[dep].add(n)
deg={n:len(set(ds)&affected) for n,ds in graph.items()};q=deque(sorted(n for n,k in deg.items() if k==0));order=[]
while q:
 n=q.popleft();order.append(n)
 for v in sorted(reverse[n]&affected):
  deg[v]-=1
  if not deg[v]:q.append(v)
need(len(order)==122,'cycle')
records={}
for n in order:
 if n in old['sources']:
  z=old['sources'][n];source=Path(z['source']);expected=z['sha256'];origin='114-source-preflight'
 elif n in ext['matched']:
  source=D/'Lean/DiophantineConsistency'/(n.split('.')[-1]+'.lean'); expected=man['source_sha256'][n];origin='peer-matched-adaptive-manifest'
 elif n in single['matched']:
  receipt=Path(single['matched'][n]['receipt']);need(sha(receipt)==single['matched'][n]['receipt_sha256'],'receipt drift '+n)
  data=json.loads(receipt.read_text());expected=data['pins']['source'];
  choices=[p for p in (D/'research').glob('**/'+n+'.lean') if '/observations/' not in str(p)]
  need(len(choices)==1,'ambiguous source '+n);source=choices[0];origin='single-object-receipt'
 else:raise RuntimeError('missing source origin '+n)
 need(source.is_file() and sha(source)==expected,'source differs '+n)
 imports=[]
 for line in source.read_text().splitlines():
  if line.startswith('import '):imports.extend(line[7:].split())
 need(set(imports)==set(graph[n])-{ 'Init' },'source/header imports differ '+n)
 records[n]={'source':str(source),'sha256':expected,'origin':origin,'imports':imports,
             'selected_object':x['project'][n]['selected']}
result={'status':'PASS_PLAN_ONLY','inputs':{str(p):sha(p) for p in (SCAN,OLD,EXTRA,MAN,PEER,SINGLE)},
        'ordered':order,'sources':records,
        'scope':'source bytes and captured import names, no rebuild; additional historical drifts can enlarge this cone'}
OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':result['status'],'modules':len(order),'sha256':sha(OUT)},sort_keys=True))
