#!/usr/bin/env python3
"""Authenticate both four-stage evaluator producers and compare their overlays."""
import hashlib,json,os
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1];BASE=Path('/tmp/nine-sharing-sign20-current-iff-check-20261109');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,m):
 if not v:raise RuntimeError(m)
u=json.loads((P/'union.json').read_text());out={}
for family,statepin,outerpin in (('20','b5a78477b7d4713fd24111c2e2f5d8a43840dd01ca40fbdddde2824c6313d47b','65fcd8c43f349184c48daf2208f5fe19b8cde4a976d3ddea12671a1b5016a0ee'),('21','a5e897bfc36ba9c7773389c52c658704b085c0932b342d1fa5f8816acf56ed72','9d5b347db282ce1fccb102d49f1ce00c4bd10c08cd1759a6a10c6c8427038c83')):
 root=Path(f'/tmp/nine-sharing-sign{family}-expression-eval-check-' + '20261109');packet=D/f'research/nine-sharing-sign{family}-expression-eval-check/attempt01';need(H(packet/'state.json')==statepin and H(packet/'outer-result.json')==outerpin,'receipt '+family);d=json.loads((packet/'state.json').read_text());o=json.loads((packet/'outer-result.json').read_text());need(d['status']=='PASS' and o['author_observed_numeric_outer_exit']==0 and len(d['rows'])==4,'status '+family)
 names=[f'Sign{family}{x}' for x in ('AbstractExpressionDef','AbstractExpressionEval','CurrentExpressionDef','CurrentExpressionEval')]
 for i,n in enumerate(names):
  r=d['rows'][i];need(r['module']==n and r['deps']['exit']==0 and r['compile']['exit']==0,'row '+n);obj=root/'lib/DiophantineConsistency'/f'{n}.olean';need(H(root/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and H(obj)==r['object_sha256'],'source/object '+n)
  for k in ('deps','compile'):need(H(root/f'{n}-{k}.txt')==r[k]['log_sha256'],'log '+n)
  for path,v in r['direct_guard'].items():
   q=Path(path)
   if v is None:need(not os.path.lexists(q),'unexpected '+path)
   else:need(q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256'],'guard '+path)
  for x in (BASE/'lib',Path('/tmp/current2011-spheres-fresh-base-priority-check02'),Path('/tmp/normalized106-fresh-model-client-20261105'),Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'),Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')):need(not os.path.lexists(x/'DiophantineConsistency'/f'{n}.olean'),'module collision '+n)
 over=0;extra={}
 for path,target in d['overlay_links'].items():
  q=Path(path);need(q.is_symlink() and str(q.resolve())==target,'overlay '+path);rel=str(q.relative_to(root/'lib'));bq=BASE/'lib'/rel
  if bq.is_file():need(H(bq)==H(q),'overlay bytes '+rel);over+=1
  else:extra[rel]={'realpath':str(q.resolve()),'sha256':H(q)}
 need(over==u[family]['overlap_count'] and extra==u[family]['extra'],'union '+family)
 for rel in extra:
  for x in (Path('/tmp/current2011-spheres-fresh-base-priority-check02'),Path('/tmp/normalized106-fresh-model-client-20261105'),Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'),Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')):need(not os.path.lexists(x/rel),'fallback collision '+rel)
 out[family]={'root':str(root),'objects':{r['module']:r['object_sha256'] for r in d['rows']},'overlap_count':over,'extra_count':len(extra)}
print(json.dumps({'status':'PASS','evaluators':out,'scope':'two successful four-stage evaluator producers and byte-matched overlays; deeper ancestry inherited'},sort_keys=True))
