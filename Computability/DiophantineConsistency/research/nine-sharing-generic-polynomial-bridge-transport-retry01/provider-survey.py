#!/usr/bin/env python3
"""Authenticate two successful provider rows within a partially failed build."""
import hashlib,json,os
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1];BASE=Path('/tmp/nine-sharing-sign28-expression-eval-check-20261106');ROOT=Path('/tmp/normalized106-fresh-model-build-v2-20261105');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,m):
 if not v:raise RuntimeError(m)
p=D/'research/normalized106-fresh-base-model-build/attempt02/state.json';need(H(p)=='c42e5d49c4234ff93e61b7dbadf63fe8e2d465f470f4772879694796d898272c','state pin');d=json.loads(p.read_text());need(d['status']=='FAILED','producer overall scope');out={}
for n in ('HAExpressionAssembly','AdaptiveEquationSyntax2011'):
 rows=[r for r in d['records'] if r['module']=='DiophantineConsistency.'+n];need(len(rows)==1,'row '+n);r=rows[0];need(r['deps_run']['exit']==0 and r['compile']['exit']==0,'successful row '+n)
 obj=ROOT/'lib/DiophantineConsistency'/f'{n}.olean';src=ROOT/'src/DiophantineConsistency'/f'{n}.lean';need(H(obj)==r['object_sha256'] and H(src)==r['source_sha256'],'source/object '+n)
 for k in ('deps_run','compile'):need(H(Path(r[k]['log']))==r[k]['log_sha256'],'log '+n+' '+k)
 for path,v in r['guard'].items():
  q=Path(path)
  if v is None:need(not os.path.lexists(q),'unexpected '+path)
  else:need(q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256'],'guard '+path)
 q=BASE/'lib/DiophantineConsistency'/f'{n}.olean';need(q.is_file() and q.resolve()==obj.resolve() and H(q)==r['object_sha256'],'base route '+n);out[n]={'sha256':r['object_sha256'],'realpath':str(obj.resolve())}
print(json.dumps({'status':'PASS','observed':out,'scope':'successful provider rows only within failed build; deeper ancestry inherited'},sort_keys=True))
