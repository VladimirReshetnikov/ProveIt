#!/usr/bin/env python3
"""Bind four direct framework imports to earlier guarded observations."""
import hashlib,json,os
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1];BASE=Path('/tmp/nine-sharing-sign32-direct-ipra-abstract-split-20261106');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
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
sp=D/'research/nine-sharing-sign32-current-source-iff-check/attempt01/state.json';need(H(sp)=='0ea9a5c9e3b04cbf28979a4c61fc7359b768ea21e0da60bcf61b1792d64f560e','source iff state pin');sd=json.loads(sp.read_text());need(sd['status']=='PASS' and len(sd['rows'])==1,'source iff status');sr=sd['rows'][0];sn='Sign32CurrentSourceIff';srroot=Path('/tmp/nine-sharing-sign32-current-source-iff-check-20261106');need(sr['module']==sn and sr['deps']['exit']==0 and sr['compile']['exit']==0,'source iff row');need(H(srroot/'src/DiophantineConsistency'/f'{sn}.lean')==sr['source_sha256'] and H(srroot/'lib/DiophantineConsistency'/f'{sn}.olean')==sr['object_sha256'],'source iff bytes')
for k in ('deps','compile'):need(H(srroot/f'{sn}-{k}.txt')==sr[k]['log_sha256'],'source iff log '+k)
for path,v in sr['direct_guard'].items():
 q=Path(path)
 if v is None:need(not os.path.lexists(q),'source iff unexpected '+path)
 else:need(q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256'],'source iff guard '+path)
q=BASE/'lib/DiophantineConsistency'/f'{sn}.olean';target=srroot/'lib/DiophantineConsistency'/f'{sn}.olean';need(q.is_file() and q.resolve()==target.resolve() and H(q)==sr['object_sha256'],'source iff overlay');result[sn]={'sha256':sr['object_sha256'],'realpath':str(target.resolve())}
print(json.dumps({'status':'PASS','observed':result,'scope':'four framework observations plus direct source iff producer; deeper ancestry inherited'},sort_keys=True))
