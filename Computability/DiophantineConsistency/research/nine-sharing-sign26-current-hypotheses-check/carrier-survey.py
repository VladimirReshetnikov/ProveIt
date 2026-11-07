#!/usr/bin/env python3
"""Bind current carrier provider to an earlier successful direct observation."""
import hashlib,json,os
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1];BASE=Path('/tmp/nine-sharing-sign26-seed-gap-check-20261106');ROOT=Path('/tmp/nine-sharing-sign33-current-windows-check-20261106');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,m):
 if not v:raise RuntimeError(m)
p=D/'research/nine-sharing-sign33-current-windows-check/attempt01';need(H(p/'state.json')=='ed0ee11bdf097d8d844da870cd9c2191f861d7e7f5e23bdf53114648f1bf64db' and H(p/'outer-observation.json')=='8ffee81f6b6c421d5b1099b344140fce00e6effba874bf558c54b80d1f23cf9c','receipt');d=json.loads((p/'state.json').read_text());o=json.loads((p/'outer-observation.json').read_text());need(d['status']=='PASS' and o['numeric_exit']==0 and len(d['rows'])==1,'status');r=d['rows'][0];n='Sign33CurrentWindows';need(r['module']==n and r['deps']['exit']==0 and r['compile']['exit']==0,'row');obj=ROOT/'lib/DiophantineConsistency'/f'{n}.olean';need(H(ROOT/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and H(obj)==r['object_sha256'],'source/object')
for k in ('deps','compile'):need(H(ROOT/f'{n}-{k}.txt')==r[k]['log_sha256'],'log '+k)
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:need(not os.path.lexists(q),'unexpected '+path)
 else:need(q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256'],'guard '+path)
rec=r['dependencies']['DiophantineConsistency.ArithmeticCarrierSoundness2011'];guard=r['direct_guard'].get(rec['path']);need(guard is not None and guard['sha256']==rec['sha256'] and guard['realpath']==rec['realpath'],'observation');q=BASE/'lib/DiophantineConsistency/ArithmeticCarrierSoundness2011.olean';need(q.is_file() and str(q.resolve())==rec['realpath'] and H(q)==rec['sha256'],'base route')
print(json.dumps({'status':'PASS','sha256':rec['sha256'],'realpath':rec['realpath'],'scope':'current carrier direct observation from earlier successful client; transitive producer ancestry inherited'},sort_keys=True))
