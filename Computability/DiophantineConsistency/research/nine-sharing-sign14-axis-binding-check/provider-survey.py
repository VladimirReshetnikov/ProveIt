#!/usr/bin/env python3
import hashlib,json,os
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise RuntimeError(m)
src=D/'research/nine-sharing-sign14-axis-degree-generic-check/attempt01/state.json';root=Path('/tmp/nine-sharing-sign14-axis-degree-generic-check-20261110');base=Path('/tmp/nine-sharing-sign14-degree-upper-check-20261110/lib')
need(sha(src)=='e6a281780e67108f016bb14ea517a17b5881decb3417f3c40620353f0c7cdebf','ingredient state');s=json.loads(src.read_text());need(s['status']=='PASS' and len(s['rows'])==1,'state status');r=s['rows'][0];n='Sign14AxisGenericDegree';need(r['module']==n and r['deps']['exit']==0 and r['compile']['exit']==0,'stage')
obj=root/'lib/DiophantineConsistency'/(n+'.olean');source=root/'src/DiophantineConsistency'/(n+'.lean');need(sha(obj)==r['object_sha256'] and sha(source)==r['source_sha256'],'producer')
for k in ('deps','compile'):need(sha(root/(n+'-'+k+'.txt'))==r[k]['log_sha256'],'log')
for k,v in r['direct_guard'].items():
 q=Path(k)
 if v is None:need(not os.path.lexists(q),'unexpected guard '+k)
 else:need(q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],'guard drift '+k)
extra={};overlap=0
for k,v in s['overlay_links'].items():
 q=Path(k);rel=q.relative_to(root/'lib');b=base/rel;need(q.is_symlink() and str(q.resolve())==v,'overlay drift '+k)
 if os.path.lexists(b):need(b.is_file() and str(b.resolve())==v and sha(b)==sha(q),'overlay mismatch '+k);overlap+=1
 else:extra[str(rel)]={'realpath':v,'sha256':sha(q)}
print(json.dumps({'status':'PASS','object_realpath':str(obj.resolve()),'object_sha256':sha(obj),'extra':extra,'overlap_count':overlap,'scope':'captured producer/union point checks, no complete transitive trace'},sort_keys=True))
