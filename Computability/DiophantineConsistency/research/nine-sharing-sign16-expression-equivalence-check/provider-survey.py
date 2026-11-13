#!/usr/bin/env python3
import hashlib,json,os
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise RuntimeError(m)
need(sha(P/'provider-pins.json')=='bfb34172099dcef5eaf1b1c7610346ff0056f7a48c561c5e359c15b9c95ddffc','pins');pins=json.loads((P/'provider-pins.json').read_text());base=Path('/tmp/nine-sharing-sign16-current-iff-check-20261110/lib');extras={};out={};overlap=0
for family,rec in pins.items():
 d=rec['directory'];root=Path('/tmp')/(d+'-'+rec['date']);state=D/'research'/d/'attempt01/state.json';need(sha(state)==rec['state_sha256'],'state '+family);s=json.loads(state.read_text());need(s['status']=='PASS' and len(s['rows'])==4,'status '+family)
 expected=['Sign'+family+x for x in ('AbstractExpressionDef','AbstractExpressionEval','CurrentExpressionDef','CurrentExpressionEval')];need([r['module'] for r in s['rows']]==expected,'stages '+family)
 for r in s['rows']:
  n=r['module'];need(r['deps']['exit']==0 and r['compile']['exit']==0,'stage '+n);obj=root/'lib/DiophantineConsistency'/(n+'.olean');src=root/'src/DiophantineConsistency'/(n+'.lean');need(sha(obj)==r['object_sha256'] and sha(src)==r['source_sha256'],'producer '+n)
  for k in ('deps','compile'):need(sha(root/(n+'-'+k+'.txt'))==r[k]['log_sha256'],'log '+n)
  for k,v in r['direct_guard'].items():
   q=Path(k)
   if v is None:need(not os.path.lexists(q),'unexpected guard '+k)
   else:need(q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],'guard '+k)
  out[n]={'object_realpath':str(obj.resolve()),'object_sha256':sha(obj)}
 for k,v in s['overlay_links'].items():
  q=Path(k);rel=str(q.relative_to(root/'lib'));b=base/rel;need(q.is_symlink() and str(q.resolve())==v,'overlay drift '+k);item={'realpath':v,'sha256':sha(q)}
  if os.path.lexists(b):need(b.is_file() and str(b.resolve())==v and sha(b)==item['sha256'],'base mismatch '+k);overlap+=1
  elif rel in extras:need(extras[rel]==item,'cross-provider mismatch '+k)
  else:extras[rel]=item
print(json.dumps({'status':'PASS','producers':out,'extra':extras,'overlap_count':overlap,'scope':'captured evaluator producers and union point checks, inherited ancestry'},sort_keys=True))
