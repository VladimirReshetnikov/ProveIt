#!/usr/bin/env python3
"""Authenticate sign28 square producers and compare source overlay."""
import hashlib,json,os
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1];BASE=Path('/tmp/nine-sharing-sign27-seed-squares-check-20261106');SRC=Path('/tmp/nine-sharing-sign28-seed-squares-check-20261106');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,m):
 if not v:raise RuntimeError(m)
p=D/'research/nine-sharing-sign28-seed-squares-check/attempt01';need(H(p/'state.json')=='441410e9dba6c3df40f03fc04825b32b0aa637e021ea219d65d373fd150d602a' and H(p/'outer-result.json')=='d646694a52855943ec600d6b459ef6483edc9bc9b8c23498b8beb3dfa9b0766d','receipt pins');d=json.loads((p/'state.json').read_text());o=json.loads((p/'outer-result.json').read_text());need(d['status']=='PASS' and len(d['rows'])==2 and o['author_observed_numeric_outer_exit']==0,'producer status')
for i,n in enumerate(('SharingSeed28Sextic','SharingSign28Squares')):
 r=d['rows'][i];need(r['module']==n and r['deps']['exit']==0 and r['compile']['exit']==0,'row '+n);obj=SRC/'lib/DiophantineConsistency'/f'{n}.olean';need(H(SRC/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and H(obj)==r['object_sha256'],'bytes '+n)
 for k in ('deps','compile'):need(H(SRC/f'{n}-{k}.txt')==r[k]['log_sha256'],'log '+n)
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:need(not os.path.lexists(q),'unexpected '+path)
  else:need(q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256'],'guard '+path)
 for root in (BASE/'lib',Path('/tmp/current2011-spheres-fresh-base-priority-check02'),Path('/tmp/normalized106-fresh-model-client-20261105'),Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'),Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')):need(not os.path.lexists(root/'DiophantineConsistency'/f'{n}.olean'),'collision '+n)
over=0
for path,target in d['overlay_links'].items():
 q=Path(path);need(q.is_symlink() and str(q.resolve())==target,'overlay '+path);rel=q.relative_to(SRC/'lib');bq=BASE/'lib'/rel;need(bq.is_file() and H(bq)==H(q),'overlay bytes '+str(rel));over+=1
need(over==1057,'overlay count')
draft=D/'research/nine-sharing-sign27-sextic-lean-draft/SharingSeed27BridgeDraft.lean';need(H(draft)=='d7c481a27d8a753a7bcafc29c0523db584097ec71ec6bdaa0ca9b7cabff5719c','bridge draft');src=(P/'src/DiophantineConsistency/Sign27FirstCut.lean').read_text();need(src.split('def lift ',1)[1].split('\n\n',1)[0]==draft.read_text().split('def lift ',1)[1].split('\n\n',1)[0],'lift mismatch')
print(json.dumps({'status':'PASS','overlap':over,'objects':{r['module']:r['object_sha256'] for r in d['rows']},'scope':'two sign28 rows/guards, byte-matched overlays and lift source; deeper ancestry inherited'},sort_keys=True))
