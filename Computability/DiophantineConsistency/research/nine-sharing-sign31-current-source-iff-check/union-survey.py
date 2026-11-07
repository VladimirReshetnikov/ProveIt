#!/usr/bin/env python3
"""Bind two reviewed overlays by byte equality and authenticate source-iff producer."""
import hashlib,json,os
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1];BASE=Path('/tmp/nine-sharing-sign31-seed-iff-check-20261106');SRC=Path('/tmp/nine-sharing-sign32-current-source-iff-check-20261106');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,m):
 if not v:raise RuntimeError(m)
u=json.loads((P/'union.json').read_text());p=D/'research/nine-sharing-sign32-current-source-iff-check/attempt01';b=D/'research/nine-sharing-sign31-seed-iff-check/attempt01'
need(H(p/'state.json')==u['source_state_sha256'] and H(p/'outer-result.json')==u['source_outer_sha256'] and H(b/'state.json')==u['base_state_sha256'],'receipt pins');d=json.loads((p/'state.json').read_text());o=json.loads((p/'outer-result.json').read_text());need(d['status']=='PASS' and len(d['rows'])==1 and o['author_observed_numeric_outer_exit']==0,'source status');r=d['rows'][0];n='Sign32CurrentSourceIff';need(r['module']==n and r['deps']['exit']==0 and r['compile']['exit']==0,'source row')
need(H(SRC/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and H(SRC/'lib/DiophantineConsistency'/f'{n}.olean')==r['object_sha256'],'source/object')
for k in ('deps','compile'):need(H(SRC/f'{n}-{k}.txt')==r[k]['log_sha256'],'source log '+k)
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:need(not os.path.lexists(q),'unexpected '+path)
 else:need(q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256'],'guard '+path)
over=0;extra={}
for path,target in d['overlay_links'].items():
 q=Path(path);need(q.is_symlink() and str(q.resolve())==target,'source overlay '+path);rel=str(q.relative_to(SRC/'lib'));bq=BASE/'lib'/rel
 if bq.is_file():need(H(bq)==H(q),'overlay byte mismatch '+rel);over+=1
 else:extra[rel]={'realpath':str(q.resolve()),'sha256':H(q)}
need(over==u['overlap_count'] and extra==u['extra'],'overlay union inventory drift')
for rel in list(extra)+['DiophantineConsistency/Sign32CurrentSourceIff.olean']:
 for root in (Path('/tmp/current2011-spheres-fresh-base-priority-check02'),Path('/tmp/normalized106-fresh-model-client-20261105'),Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'),Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')):need(not os.path.lexists(root/rel),'fallback collision '+str(root/rel))
need(not os.path.lexists(BASE/'lib/DiophantineConsistency/Sign32CurrentSourceIff.olean'),'source object collision')
print(json.dumps({'status':'PASS','overlap':over,'injected_extra':len(extra),'scope':'point-in-time source row and byte-matched overlay union; deeper ancestry inherited'},sort_keys=True))
