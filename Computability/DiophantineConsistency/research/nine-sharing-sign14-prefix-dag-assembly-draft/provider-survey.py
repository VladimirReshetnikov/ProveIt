#!/usr/bin/env python3
"""Point survey of the expression provider against the DAG-decode overlay."""
import hashlib,json,os
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise RuntimeError(m)
src=D/'research/nine-sharing-sign14-expression-eval-check/attempt01/state.json';root=Path('/tmp/nine-sharing-sign14-expression-eval-check-20261110');base=Path('/tmp/nine-sharing-sign14-prefix-dag-decode-check-20261110/lib')
need(sha(src)=='2845701170bad15d792b2a893bae1635e2878b2b5ebe00904aab0ebae2da8e38','expression state');s=json.loads(src.read_text());need(s['status']=='PASS' and len(s['rows'])==4,'state status')
for row in s['rows']:
 n=row['module'];need(row['deps']['exit']==0 and row['compile']['exit']==0,'stage '+n);need(sha(root/'src/DiophantineConsistency'/(n+'.lean'))==row['source_sha256'] and sha(root/'lib/DiophantineConsistency'/(n+'.olean'))==row['object_sha256'],'source/object '+n)
 for k in ('deps','compile'):need(sha(root/(n+'-'+k+'.txt'))==row[k]['log_sha256'],'log '+n)
 for k,v in row['direct_guard'].items():
  q=Path(k)
  if v is None:need(not os.path.lexists(q),'unexpected guard '+k)
  else:need(q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],'guard drift '+k)
extra={};overlap=0
for k,v in s['overlay_links'].items():
 q=Path(k);rel=q.relative_to(root/'lib');b=base/rel;need(q.is_symlink() and str(q.resolve())==v,'overlay drift '+k)
 if os.path.lexists(b):need(b.is_file() and str(b.resolve())==v and sha(b)==sha(q),'overlay mismatch '+k);overlap+=1
 else:extra[str(rel)]={'realpath':v,'sha256':sha(q)}
r=s['rows'][0];need(r['module']=='Sign14AbstractExpressionDef','expression definition row');obj=root/'lib/DiophantineConsistency/Sign14AbstractExpressionDef.olean'
print(json.dumps({'status':'PASS','object_realpath':str(obj.resolve()),'object_sha256':sha(obj),'extra':extra,'overlap_count':overlap,'scope':'captured producer/union point checks, no complete transitive trace'},sort_keys=True))
