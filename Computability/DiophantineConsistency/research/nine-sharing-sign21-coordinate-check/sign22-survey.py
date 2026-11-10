#!/usr/bin/env python3
"""Authenticate both sign22 producer rows and their shared dependency routes."""
import hashlib,json,os
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1];ROOT=Path('/tmp/nine-sharing-sign22-seed-squares-check-20261109');BASE=Path('/tmp/nine-sharing-sign21-seed-squares-check-20261109');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,m):
 if not v:raise RuntimeError(m)
p=D/'research/nine-sharing-sign22-seed-squares-check/attempt01';need(H(p/'state.json')=='056e1b6b024b993983c26c2a5fcc02edcbb0bc859310a8830b9960e0cc032d1f' and H(p/'outer-result.json')=='5a5b6671d7da5d21800aa5707ea39ba3c80ae0ce8466aad22b669750322eb384','receipt pins');d=json.loads((p/'state.json').read_text());o=json.loads((p/'outer-result.json').read_text());need(d['status']=='PASS' and len(d['rows'])==2 and o['author_observed_numeric_outer_exit']==0,'producer status');result={}
for i,name in enumerate(('SharingSeed22Dodecic','SharingSign22Squares')):
 r=d['rows'][i];need(r['module']==name and r['deps']['exit']==0 and r['compile']['exit']==0,'row '+name);obj=ROOT/'lib/DiophantineConsistency'/f'{name}.olean';need(H(ROOT/'src/DiophantineConsistency'/f'{name}.lean')==r['source_sha256'] and H(obj)==r['object_sha256'],'source/object '+name)
 for k in ('deps','compile'):need(H(ROOT/f'{name}-{k}.txt')==r[k]['log_sha256'],'log '+name)
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:need(not os.path.lexists(q),'unexpected '+path)
  else:need(q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256'],'guard '+path)
 for dep,rec in r['dependencies'].items():
  short=dep.split('.')[-1]
  if short in ('Init','SharingSeed22Dodecic'):continue
  q=BASE/'lib'/Path(dep.replace('.','/')+'.olean');need(q.is_file() and str(q.resolve())==rec['realpath'] and H(q)==rec['sha256'],'shared route '+dep)
 q=BASE/'lib/DiophantineConsistency'/f'{name}.olean';need(not os.path.lexists(q),'base collision '+name)
 for root in (Path('/tmp/current2011-spheres-fresh-base-priority-check02'),Path('/tmp/normalized106-fresh-model-client-20261105'),Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'),Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')):need(not os.path.lexists(root/'DiophantineConsistency'/f'{name}.olean'),'fallback collision '+name)
 result[name]={'sha256':r['object_sha256'],'realpath':str(obj.resolve())}
print(json.dumps({'status':'PASS','observed':result,'scope':'two sign22 producer rows and shared direct dependency routes; deeper ancestry inherited'},sort_keys=True))
