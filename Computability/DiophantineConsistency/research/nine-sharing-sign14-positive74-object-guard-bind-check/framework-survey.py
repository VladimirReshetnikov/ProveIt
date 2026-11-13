#!/usr/bin/env python3
"""Bind four direct framework imports to earlier guarded observations."""
import hashlib,json,os
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1];BASE=Path('/tmp/nine-sharing-sign14-positive74-object-guard-reconstruct-check-20261110');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
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
q=BASE/'lib/DiophantineConsistency'/'IPRAPredReconstruct.olean';need(q.is_file() and str(q.resolve())=='/tmp/current14-standard-fresh-build-20261104/lib/DiophantineConsistency/IPRAPredReconstruct.olean' and H(q)=='9fbab89a20bfc8373b7b1e2706700d783007f2d4ffabe97fd889c2e48d4625d4','historical point pin IPRAPredReconstruct');result['IPRAPredReconstruct']={'sha256':'9fbab89a20bfc8373b7b1e2706700d783007f2d4ffabe97fd889c2e48d4625d4','realpath':'/tmp/current14-standard-fresh-build-20261104/lib/DiophantineConsistency/IPRAPredReconstruct.olean'}
q=BASE/'lib/DiophantineConsistency'/'IPRANativeAtomStability.olean';need(q.is_file() and str(q.resolve())=='/tmp/current14-standard-fresh-build-20261104/lib/DiophantineConsistency/IPRANativeAtomStability.olean' and H(q)=='8ff01b95e164af4728c37fd64c9179a0e89c883a6b05aa5c98539d9032db88a7','historical point pin IPRANativeAtomStability');result['IPRANativeAtomStability']={'sha256':'8ff01b95e164af4728c37fd64c9179a0e89c883a6b05aa5c98539d9032db88a7','realpath':'/tmp/current14-standard-fresh-build-20261104/lib/DiophantineConsistency/IPRANativeAtomStability.olean'}
q=BASE/'lib/DiophantineConsistency'/'IPRATheoryInstantiation.olean';need(q.is_file() and str(q.resolve())=='/tmp/current14-standard-fresh-build-20261104/lib/DiophantineConsistency/IPRATheoryInstantiation.olean' and H(q)=='3fdbddcc7ad94c70e15baa226688d1f5844ac6eae7eb490b523d8c910b9f2257','historical point pin IPRATheoryInstantiation');result['IPRATheoryInstantiation']={'sha256':'3fdbddcc7ad94c70e15baa226688d1f5844ac6eae7eb490b523d8c910b9f2257','realpath':'/tmp/current14-standard-fresh-build-20261104/lib/DiophantineConsistency/IPRATheoryInstantiation.olean'}
q=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib/Foundation/Meta/IntProver.olean');need(q.is_file() and str(q.resolve())=='/tmp/ipra-foundation-guarded-v2-cjHUaJun/.lake/build/lib/lean/Foundation/Meta/IntProver.olean' and H(q)=='18ab1dc383fb9eb941745bff4e84fb86f09a97f2a048f8e14dc489f662eea5f3','historical point pin IntProver');result['IntProver']={'sha256':'18ab1dc383fb9eb941745bff4e84fb86f09a97f2a048f8e14dc489f662eea5f3','realpath':'/tmp/ipra-foundation-guarded-v2-cjHUaJun/.lake/build/lib/lean/Foundation/Meta/IntProver.olean'}
print(json.dumps({'status':'PASS','observed':result,'scope':'four direct framework objects tied to earlier direct guards; their own producer ancestry inherited'},sort_keys=True))
