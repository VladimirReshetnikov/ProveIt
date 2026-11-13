#!/usr/bin/env python3
import hashlib,json,os
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise RuntimeError(m)
need(sha(P/'provider-pins.json')=='e5e7ead4907ec2198678dd0af50ad72411079e2136d2a4de558b823bc5cc071a','provider manifest pin');pins=json.loads((P/'provider-pins.json').read_text())
base=Path('/tmp/nine-sharing-sign16-scalar-window-retry01-check-20261110/lib');out={}
for family,rec in pins.items():
 d=rec['directory'];n=rec['module'];state=D/'research'/d/'attempt01/state.json';root=Path('/tmp')/(d+'-20261110')
 need(sha(state)==rec['state_sha256'],'state drift '+family);s=json.loads(state.read_text());need(s['status']=='PASS' and len(s['rows'])==1,'state status '+family);r=s['rows'][0];need(r['module']==n and r['deps']['exit']==0 and r['compile']['exit']==0,'stage '+family)
 obj=root/'lib/DiophantineConsistency'/(n+'.olean');src=root/'src/DiophantineConsistency'/(n+'.lean');need(sha(obj)==r['object_sha256'] and sha(src)==r['source_sha256'],'producer '+family)
 for k in ('deps','compile'):need(sha(root/(n+'-'+k+'.txt'))==r[k]['log_sha256'],'log '+family)
 for k,v in r['direct_guard'].items():
  q=Path(k)
  if v is None:need(not os.path.lexists(q),'guard unexpected '+k)
  else:need(q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],'guard drift '+k)
 for k,v in s['overlay_links'].items():
  q=Path(k);b=base/q.relative_to(root/'lib');need(q.is_symlink() and str(q.resolve())==v and b.is_file() and str(b.resolve())==v and sha(b)==sha(q),'overlay mismatch '+k)
 out[family]={'object_realpath':str(obj.resolve()),'object_sha256':sha(obj),'module':n,'overlay_count':len(s['overlay_links'])}
print(json.dumps({'status':'PASS','producers':out,'scope':'provider and overlay point checks, no complete transitive trace'},sort_keys=True))
