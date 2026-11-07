#!/usr/bin/env python3
"""Authenticate the standalone ordered-ring provider and direct guards."""
import hashlib,json,os
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1];ROOT=Path('/tmp/sign26-ordered-ring-retry01-20261106');BASE=Path('/tmp/nine-sharing-sign26-seed-squares-check-20261106');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,m):
 if not v:raise RuntimeError(m)
p=D/'research/nine-sharing-sign26-ordered-ring-retry01/attempt01';need(H(p/'state.json')=='5e8eecb6b7e02494b212f9ed17591d5db80c6068def201d16c1bac29203428a9' and H(p/'outer-result.json')=='a336db3d9e62a8fcda4468c3ceb7225d3a334ec058a7964d6aa154071fa165e1','receipt pins');d=json.loads((p/'state.json').read_text());o=json.loads((p/'outer-result.json').read_text());need(d['status']=='PASS' and o['author_observed_numeric_outer_exit']==0 and len(d['rows'])==1,'status');r=d['rows'][0];need(r['module']=='Sign26OrderedRing' and r['deps']['exit']==0 and r['compile']['exit']==0,'stage');obj=ROOT/'lib/Sign26OrderedRing.olean';need(H(ROOT/'src/Sign26OrderedRing.lean')==r['source_sha256'] and H(obj)==r['object_sha256'],'source/object')
for k in ('deps','compile'):need(H(ROOT/f'Sign26OrderedRing-{k}.txt')==r[k]['log_sha256'],'log '+k)
for path,v in d['direct_guard'].items():
 q=Path(path)
 if v is None:need(not os.path.lexists(q),'unexpected '+path)
 else:need(q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256'],'guard '+path)
for root in (BASE/'lib',Path('/tmp/current2011-spheres-fresh-base-priority-check02'),Path('/tmp/normalized106-fresh-model-client-20261105'),Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'),Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')):need(not os.path.lexists(root/'Sign26OrderedRing.olean'),'candidate collision')
print(json.dumps({'status':'PASS','object_sha256':r['object_sha256'],'object_realpath':str(obj.resolve()),'scope':'standalone ordered-ring provider and 80 direct guards; deeper ancestry inherited'},sort_keys=True))
