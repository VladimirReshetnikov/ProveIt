#!/usr/bin/env python3
"""Pin a 127-module source plan after the HA87 dependency comparison."""
from collections import defaultdict,deque
from hashlib import sha256
from pathlib import Path
import json
H=Path(__file__).resolve().parent;D=H.parents[1]
SCAN=D/'reviews/ten-positive-80-fixed-ipra-serialized-closure/observations/attempt01/result.json'
OLD=D/'reviews/ten-positive-80-expanded-rebuild-preflight/observations/attempt01.json'
DRIFT=D/'reviews/ten-positive-80-ha87-producer-drift/observations/attempt01.json'
MAN=D/'reviews/ipra-adaptive-native-fixed-continuation/manifest.json'
PEER=D/'reviews/ipra-adaptive-native-fixed-continuation-verification-peer/receipt.json'
OUT=H/'observations/attempt01.json'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(not OUT.exists(),'output exists')
x=json.loads(SCAN.read_text());old=json.loads(OLD.read_text());dr=json.loads(DRIFT.read_text());man=json.loads(MAN.read_text());peer=json.loads(PEER.read_text())
need(sha(MAN)==peer['manifest_sha256'] and peer['status']=='MATCHED_PASS','manifest mismatch')
affected=set(dr['affected']);need(len(affected)==127 and set(old['ordered'])<=affected,'unexpected cone')
graph={n:x['fresh_headers'][n] for n in affected};reverse=defaultdict(set)
for n,ds in graph.items():
 for dep in ds:reverse[dep].add(n)
degree={n:len(set(ds)&affected) for n,ds in graph.items()};q=deque(sorted(n for n,k in degree.items() if not k));order=[]
while q:
 n=q.popleft();order.append(n)
 for client in sorted(reverse[n]&affected):
  degree[client]-=1
  if not degree[client]:q.append(client)
need(len(order)==127 and order[-1]=='Direct80SymbolicFixedIPRA','cycle/endpoint')
records={}
for n in order:
 if n in old['sources']:
  z=old['sources'][n];source=Path(z['source']);expected=z['sha256'];origin='122-source-preflight'
 elif n in dr['records']:
  source=D/'Lean/DiophantineConsistency'/(n.split('.')[-1]+'.lean');expected=dr['records'][n]['historical_record']['source_sha256'];origin='byte-matched-ha87-author-state'
 else:
  need(n=='DiophantineConsistency.ArithmeticAdaptiveWindowCore2011','unexpected new module '+n)
  record=man['prefix_records'][n];need(record['object_sha256']==x['project'][n]['selected']['sha256'],'prefix object mismatch')
  source=D/'Lean/DiophantineConsistency'/(n.split('.')[-1]+'.lean');expected=man['source_sha256'][n];origin='peer-matched-adaptive-prefix-manifest'
 need(source.is_file() and sha(source)==expected,'source drift '+n)
 imports=[]
 for line in source.read_text().splitlines():
  if line.startswith('import '):imports.extend(line[7:].split())
 need(set(imports)==set(graph[n])-{'Init'},'source/header imports differ '+n)
 records[n]={'source':str(source),'sha256':expected,'origin':origin,'imports':imports,'selected_object':x['project'][n]['selected']}
result={'status':'PASS_PLAN_ONLY','inputs':{str(p):sha(p) for p in (SCAN,OLD,DRIFT,MAN,PEER)},'ordered':order,'sources':records,
        'scope':'source bytes and serialized import names only; no rebuild; additional historical mismatch may enlarge cone'}
OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':result['status'],'modules':len(order),'sha256':sha(OUT)},sort_keys=True))
