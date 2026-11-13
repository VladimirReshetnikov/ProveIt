#!/usr/bin/env python3
"""Authenticate both sign19 producer rows and their shared dependency routes."""
import hashlib,json,os
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1];ROOT=Path('/tmp/nine-sharing-sign19-staged-syntax-check-20261110');BASE=Path('/tmp/nine-sharing-sign18-staged-syntax-check-20261110');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,m):
 if not v:raise RuntimeError(m)
p=D/'research/nine-sharing-sign19-staged-syntax-check/attempt01';need(H(p/'state.json')=='221520bd6603560ede0f8e87c68938cb95f06fd18a2522ce4002ea08c12b67dd' and H(p/'outer-result.json')=='eced6d4b9626969b3b47c4b96edaee56b7ade097d05d833355bd34bd6a3bc6a6','receipt pins');d=json.loads((p/'state.json').read_text());o=json.loads((p/'outer-result.json').read_text());need(d['status']=='PASS' and len(d['rows'])==12 and o['author_observed_numeric_outer_exit']==0,'producer status');result={}
names=[f'SharingSeed19Row{i:02}' for i in range(10)]+['SharingSeed19Degree44','SharingSign19Squares']
for i,name in enumerate(names):
 r=d['rows'][i];need(r['module']==name and r['deps']['exit']==0 and r['compile']['exit']==0,'row '+name);obj=ROOT/'lib/DiophantineConsistency'/f'{name}.olean';need(H(ROOT/'src/DiophantineConsistency'/f'{name}.lean')==r['source_sha256'] and H(obj)==r['object_sha256'],'source/object '+name)
 for k in ('deps','compile'):need(H(ROOT/f'{name}-{k}.txt')==r[k]['log_sha256'],'log '+name)
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:need(not os.path.lexists(q),'unexpected '+path)
  else:need(q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256'],'guard '+path)
 for dep,rec in r['dependencies'].items():
  short=dep.split('.')[-1]
  if short=='Init':continue
  if short in names:
   q=ROOT/'lib'/Path(dep.replace('.','/')+'.olean');need(q.is_file() and str(q.resolve())==rec['realpath'] and H(q)==rec['sha256'],'staged route '+dep);continue
  q=BASE/'lib'/Path(dep.replace('.','/')+'.olean');need(q.is_file() and str(q.resolve())==rec['realpath'] and H(q)==rec['sha256'],'shared route '+dep)
 q=BASE/'lib/DiophantineConsistency'/f'{name}.olean';need(not os.path.lexists(q),'base collision '+name)
 for root in (Path('/tmp/current2011-spheres-fresh-base-priority-check02'),Path('/tmp/normalized106-fresh-model-client-20261105'),Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'),Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')):need(not os.path.lexists(root/'DiophantineConsistency'/f'{name}.olean'),'fallback collision '+name)
 result[name]={'sha256':r['object_sha256'],'realpath':str(obj.resolve())}
print(json.dumps({'status':'PASS','observed':result,'scope':'twelve sign19 producer rows and shared direct dependency routes; deeper ancestry inherited'},sort_keys=True))
