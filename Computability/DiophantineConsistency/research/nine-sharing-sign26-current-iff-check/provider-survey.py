#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site: raise SystemExit('use python3 -I -S -B')
p=Path(__file__).resolve().parent; d=p.parents[1]
def sha(q):return hashlib.sha256(Path(q).read_bytes()).hexdigest()
def need(c,m):
 if not c: raise RuntimeError(m)
sp=d/'research/nine-sharing-sign26-current-hypotheses-check/attempt01/state.json';base=Path('/tmp/nine-sharing-sign26-current-hypotheses-check-20261106'); bp=d/'research/nine-sharing-sign26-seed-iff-check/attempt01/state.json';bb=Path('/tmp/nine-sharing-sign26-seed-iff-check-20261106')
need(sha(sp)=='0804fe71996cf494065b75b1841dabd289c4de523b6ea0478d2cc49c9d74e2dc','current state');need(sha(bp)=='653384ed8fddb2d0e1e5f7e2a2a56ba90078ad313ffbddabf316712d3b5f7a2a','iff state');s=json.loads(sp.read_text());b=json.loads(bp.read_text());need(s['status']=='PASS' and b['status']=='PASS' and len(s['rows'])==1,'status');r=s['rows'][0];n='Sign26CurrentHypotheses';need(r['module']==n and r['deps']['exit']==0 and r['compile']['exit']==0,'stage');obj=base/'lib/DiophantineConsistency'/(n+'.olean');src=base/'src/DiophantineConsistency'/(n+'.lean');need(sha(obj)==r['object_sha256'] and sha(src)==r['source_sha256'],'source/object')
for k in ('deps','compile'):need(sha(base/(n+'-'+k+'.txt'))==r[k]['log_sha256'],'log '+k)
for k,v in r['direct_guard'].items():
 q=Path(k)
 if v is None:need(not os.path.lexists(q),'unexpected '+k)
 else:need(q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],'guard '+k)
x={str(Path(k).relative_to(bb/'lib')):v for k,v in b['overlay_links'].items()};y={str(Path(k).relative_to(base/'lib')):v for k,v in s['overlay_links'].items()}
for rel,v in y.items():
 q=base/'lib'/rel;need(q.is_symlink() and str(q.resolve())==v,'link '+rel);need(rel in x and Path(x[rel]).resolve()==Path(v).resolve() and sha(x[rel])==sha(v),'overlap '+rel)
print(json.dumps({'status':'PASS','object_realpath':str(obj.resolve()),'object_sha256':sha(obj),'common_count':len(y),'extra_count':0},sort_keys=True))
