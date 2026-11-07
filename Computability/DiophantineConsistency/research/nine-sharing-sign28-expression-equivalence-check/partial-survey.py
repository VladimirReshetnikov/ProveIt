#!/usr/bin/env python3
"""Authenticate the successful first row within the failed factored retry."""
import hashlib,json,os
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1];ROOT=Path('/tmp/nine-sharing-sign28-current-source-iff-retry01-20261106');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,m):
 if not v:raise RuntimeError(m)
p=D/'research/nine-sharing-sign28-current-source-iff-retry01/attempt01'
need(H(p/'state.json')=='dfc94dbdc92becb9dc3971a1a999461f60fee832203f55371be933c5acfa9f93' and H(p/'outer-result.json')=='f80fcf0add0d96a2003b5230b3d5c7f0f15060c3fdfb95f0e56b782b4567005b','receipt pins')
d=json.loads((p/'state.json').read_text());o=json.loads((p/'outer-result.json').read_text());need(d['status']=='FAILED' and len(d['rows'])==2 and o['author_observed_numeric_outer_exit']==1,'partial status')
r=d['rows'][0];n='Sign28CurrentConsIff';need(r['module']==n and r['deps']['exit']==0 and r['compile']['exit']==0,'first stage')
obj=ROOT/'lib/DiophantineConsistency'/f'{n}.olean';need(H(ROOT/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and H(obj)==r['object_sha256'],'source/object')
for k in ('deps','compile'):need(H(ROOT/f'{n}-{k}.txt')==r[k]['log_sha256'],'log '+k)
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:need(not os.path.lexists(q),'unexpected '+path)
 else:need(q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256'],'guard '+path)
for path,target in d['overlay_links'].items():need(Path(path).is_symlink() and str(Path(path).resolve())==target,'overlay '+path)
for root in ('/tmp/nine-sharing-sign28-current-iff-check-20261106/lib','/tmp/current2011-spheres-fresh-base-priority-check02','/tmp/normalized106-fresh-model-client-20261105','/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib','/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean'):
 need(not os.path.lexists(Path(root)/'DiophantineConsistency/Sign28CurrentConsIff.olean'),'cons candidate collision '+root)
print(json.dumps({'status':'PASS','object_sha256':r['object_sha256'],'object_realpath':str(obj.resolve()),'scope':'successful first stage only; no final postflight or failed-stage theorem'},sort_keys=True))
