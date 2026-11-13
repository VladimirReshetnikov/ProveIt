#!/usr/bin/env python3
"""Authenticate both four-stage evaluator producers and compare their overlays."""
import hashlib,json,os
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1];BASE=Path('/tmp/nine-sharing-sign25-seed-iff-check-20261106');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,m):
 if not v:raise RuntimeError(m)
u=json.loads((P/'union.json').read_text());out={}
for family,statepin,outerpin in (('25','509b12bca5b8565217a8498d9a7489e7ea363da7df87720a0abbf4519fa664bf','773ab308fa8910ec27dc609e449a90121ca4289b792fa9ec213ed8c0d70170df'),('26','2deb0d1a6bf67cd0829ba1f16a2bea1f02bb9637bf2625ca3c4ce926fc3c6378','84199558f4a67594155e865f654c638de6e59e29b10fa93759c07426c1408da0')):
 root=Path(f'/tmp/nine-sharing-sign{family}-expression-eval-check-20261106');packet=D/f'research/nine-sharing-sign{family}-expression-eval-check/attempt01';need(H(packet/'state.json')==statepin and H(packet/'outer-result.json')==outerpin,'receipt '+family);d=json.loads((packet/'state.json').read_text());o=json.loads((packet/'outer-result.json').read_text());need(d['status']=='PASS' and o['author_observed_numeric_outer_exit']==0 and len(d['rows'])==4,'status '+family)
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
