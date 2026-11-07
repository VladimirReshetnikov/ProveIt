#!/usr/bin/env python3
"""Authenticate all three prior cut objects and drop-source identity."""
import hashlib,json,os
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1];ROOT=Path('/tmp/nine-sharing-sign28-first-cuts-check-20261106');BASE=Path('/tmp/nine-sharing-sign28-remaining-cuts-check-20261106');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,m):
 if not v:raise RuntimeError(m)
p=D/'research/nine-sharing-sign28-first-cuts-check/attempt01';need(H(p/'state.json')=='82098b8677786e00940171383444350049b1b266251508e8fb138cb77e62d9b8' and H(p/'outer-result.json')=='6d9d157ace0ff2aa298b648ba843d9b93d7dc04aa4a81c797950a75d99d94b26','receipt pins');d=json.loads((p/'state.json').read_text());o=json.loads((p/'outer-result.json').read_text());need(d['status']=='PASS' and len(d['rows'])==3 and o['author_observed_numeric_outer_exit']==0,'producer status');out=[]
for i in range(3):
 n=f'Sign28FirstCuts{i:02d}';r=d['rows'][i];need(r['module']==n and r['deps']['exit']==0 and r['compile']['exit']==0,'row '+n);obj=ROOT/'lib/DiophantineConsistency'/f'{n}.olean';need(H(ROOT/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and H(obj)==r['object_sha256'],'source/object '+n)
 for k in ('deps','compile'):need(H(ROOT/f'{n}-{k}.txt')==r[k]['log_sha256'],'log '+n)
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:need(not os.path.lexists(q),'unexpected '+path)
  else:need(q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256'],'guard '+path)
 q=BASE/'lib/DiophantineConsistency'/f'{n}.olean';need(q.is_file() and q.resolve()==obj.resolve() and H(q)==r['object_sha256'],'overlay route '+n);out.append(r['object_sha256'])
draft=D/'research/nine-sharing-sign28-sextic-lean-draft/SharingSeed28BridgeDraft.lean';need(H(draft)=='54a5790f5dca97bce9a79cc32b96d7a320195be72f3aec51db59d1cdb9d68e9c','bridge draft pin');src=(P/'src/DiophantineConsistency/Sign28CoordinateDrop.lean').read_text();need(src.split('def drop ',1)[1].split('\n\n',1)[0]==draft.read_text().split('def drop ',1)[1].split('\n\n',1)[0],'drop definition mismatch')
print(json.dumps({'status':'PASS','objects':out,'scope':'three cut producers/guards and drop source; deeper ancestry inherited'},sort_keys=True))
