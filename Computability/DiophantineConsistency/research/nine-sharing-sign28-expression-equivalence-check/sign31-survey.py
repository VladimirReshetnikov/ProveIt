#!/usr/bin/env python3
"""Authenticate the four successful expression rows in a failed producer."""
import hashlib,json,os
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1];BASE=Path('/tmp/nine-sharing-sign28-expression-eval-check-20261106');SRC=Path('/tmp/nine-sharing-sign31-direct-ipra-retry01-20261106');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,m):
 if not v:raise RuntimeError(m)
p=D/'research/nine-sharing-sign31-direct-ipra-retry01/attempt01';u=json.loads((P/'union.json').read_text())
need(H(p/'state.json')==u['source_state_sha256'] and H(p/'outer-result.json')==u['source_outer_sha256'],'source receipts');d=json.loads((p/'state.json').read_text());o=json.loads((p/'outer-result.json').read_text());need(d['status']=='FAILED' and o['author_observed_numeric_outer_exit']==1 and len(d['rows'])==6,'partial status')
for i,n in enumerate(('Sign31AbstractExpressionDef','Sign31AbstractExpressionEval','Sign31CurrentExpressionDef','Sign31CurrentExpressionEval')):
 r=d['rows'][i];need(r['module']==n and r['deps']['exit']==0 and r['compile']['exit']==0,'row '+n)
 need(H(SRC/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and H(SRC/'lib/DiophantineConsistency'/f'{n}.olean')==r['object_sha256'],'source/object '+n)
 for k in ('deps','compile'):need(H(SRC/f'{n}-{k}.txt')==r[k]['log_sha256'],'log '+n)
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:need(not os.path.lexists(q),'unexpected '+path)
  else:need(q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256'],'guard '+path)
 for root in (BASE/'lib',Path('/tmp/current2011-spheres-fresh-base-priority-check02'),Path('/tmp/normalized106-fresh-model-client-20261105'),Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'),Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')):need(not os.path.lexists(root/'DiophantineConsistency'/f'{n}.olean'),'candidate collision '+n)
over=0;extra={}
for path,target in d['overlay_links'].items():
 q=Path(path);need(q.is_symlink() and str(q.resolve())==target,'source overlay '+path);rel=str(q.relative_to(SRC/'lib'));bq=BASE/'lib'/rel
 if bq.is_file():need(H(bq)==H(q),'overlay bytes '+rel);over+=1
 else:extra[rel]={'realpath':str(q.resolve()),'sha256':H(q)}
need(over==u['overlap_count'] and extra==u['extra'],'union mismatch')
for rel in extra:
 for root in (Path('/tmp/current2011-spheres-fresh-base-priority-check02'),Path('/tmp/normalized106-fresh-model-client-20261105'),Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'),Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')):need(not os.path.lexists(root/rel),'fallback collision '+rel)
print(json.dumps({'status':'PASS','overlap':over,'injected_extra':len(extra),'scope':'four successful sign31 expression rows only; later failed stage excluded; deeper ancestry inherited'},sort_keys=True))
