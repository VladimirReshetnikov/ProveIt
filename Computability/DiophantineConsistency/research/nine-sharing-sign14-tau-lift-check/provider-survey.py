#!/usr/bin/env python3
import hashlib,json,os
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise RuntimeError(m)
need(sha(P/'provider-pins.json')=='3881f73016be3c359a05461058b9b2f8e737f0cca9d49f715748648b6f110659','pins');pins=json.loads((P/'provider-pins.json').read_text());base=Path('/tmp/nine-sharing-sign14-tau-bound-check-20261110/lib');extras={};out={};overlap=0
for family,rec in pins.items():
 d=rec['directory'];n=rec['module'];root=Path('/tmp')/(d+'-'+rec['date']);state=D/'research'/d/'attempt01/state.json'
 need(sha(state)==rec['state_sha256'],'state '+family);s=json.loads(state.read_text());need(s['status']=='PASS' and len(s['rows'])==1,'status '+family);r=s['rows'][0];need(r['module']==n and r['deps']['exit']==0 and r['compile']['exit']==0,'stage '+family)
 obj=root/'lib/DiophantineConsistency'/(n+'.olean');source=root/'src/DiophantineConsistency'/(n+'.lean');need(sha(obj)==r['object_sha256'] and sha(source)==r['source_sha256'],'producer '+family)
 for k in ('deps','compile'):need(sha(root/(n+'-'+k+'.txt'))==r[k]['log_sha256'],'log '+family)
 for k,v in r['direct_guard'].items():
  q=Path(k)
  if v is None:need(not os.path.lexists(q),'unexpected guard '+k)
  else:need(q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],'guard drift '+k)
 for k,v in s['overlay_links'].items():
  q=Path(k);rel=str(q.relative_to(root/'lib'));b=base/rel;need(q.is_symlink() and str(q.resolve())==v,'overlay drift '+k);record={'realpath':v,'sha256':sha(q)}
  if os.path.lexists(b):need(b.is_file() and str(b.resolve())==v and sha(b)==record['sha256'],'base mismatch '+k);overlap+=1
  elif rel in extras:need(extras[rel]==record,'cross-provider mismatch '+k)
  else:extras[rel]=record
 out[n]={'object_realpath':str(obj.resolve()),'object_sha256':sha(obj)}
print(json.dumps({'status':'PASS','producers':out,'extra':extras,'overlap_count':overlap,'scope':'captured producers and union point checks, no complete transitive trace'},sort_keys=True))
