#!/usr/bin/env python3
"""Bind four direct framework imports to earlier guarded observations."""
import hashlib,json,os
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1];BASE=Path('/tmp/nine-sharing-sign23-concrete-polynomial-bridge-check-20261109');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,m):
 if not v:raise RuntimeError(m)
checks=[('research/nine-current-fresh-jones-client/attempt01/state.json','469b279c32677e416e757dcd59835ea0514d1e524338d3c451ae8cfa8e446439','/tmp/nine-fresh-jones-client-20261105',('ModelJonesSyntax',)),('research/nine-sharing-sign33-ipra-endpoint-check/attempt01/state.json','451878b602e716cd712c2e8709e3546c13e5dbcc7c1ff7edc6dc669b640a4338','/tmp/nine-sharing-sign33-ipra-endpoint-check-20261106',('HACurrentEquation2011','IPRAExpressionNative','IPRAStandardTheory'))]
result={}
for state,pin,root,names in checks:
 state=D/state;root=Path(root);need(H(state)==pin,'state pin');d=json.loads(state.read_text());need(d['status']=='PASS' and len(d['rows'])==1,'state');r=d['rows'][0];n=r['module'];need(r['deps']['exit']==0 and r['compile']['exit']==0,'producer status '+n)
 need(H(root/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and H(root/'lib/DiophantineConsistency'/f'{n}.olean')==r['object_sha256'],'producer bytes '+n)
 for k in ('deps','compile'):need(H(root/f'{n}-{k}.txt')==r[k]['log_sha256'],'producer log '+n)
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:need(not os.path.lexists(q),'unexpected '+path)
  else:need(q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256'],'guard '+path)
 for name in names:
  rec=r['dependencies']['DiophantineConsistency.'+name];g=r['direct_guard'].get(rec['path']);need(g is not None and g['sha256']==rec['sha256'] and g['realpath']==rec['realpath'],'observation '+name)
  q=BASE/'lib/DiophantineConsistency'/f'{name}.olean';need(q.is_file() and str(q.resolve())==rec['realpath'] and H(q)==rec['sha256'],'overlay '+name);result[name]={'sha256':rec['sha256'],'realpath':rec['realpath']}
print(json.dumps({'status':'PASS','observed':result,'scope':'four direct framework objects tied to earlier direct guards; their own producer ancestry inherited'},sort_keys=True))
