#!/usr/bin/env python3
"""Authenticate the transitive first-cut object used directly by bridge terms."""
import hashlib,json,os
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1];ROOT=Path('/tmp/nine-sharing-sign25-first-cut-check-20261106');BASE=Path('/tmp/nine-sharing-sign25-remaining-cuts-check-20261106');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,m):
 if not v:raise RuntimeError(m)
p=D/'research/nine-sharing-sign25-first-cut-check/attempt01';need(H(p/'state.json')=='363ca49f42af37fac085571d5c662bfae1aea1b9bd7c2c04b5a268ae5c68c1a6' and H(p/'outer-result.json')=='71ce9cb13b491220d312251df3e4ee23656a0d8d9f7a414b54dcb56cfb138a91','receipt pins');d=json.loads((p/'state.json').read_text());o=json.loads((p/'outer-result.json').read_text());need(d['status']=='PASS' and len(d['rows'])==1 and o['author_observed_numeric_outer_exit']==0,'producer status');r=d['rows'][0];n='Sign25FirstCut';need(r['module']==n and r['deps']['exit']==0 and r['compile']['exit']==0,'row');obj=ROOT/'lib/DiophantineConsistency'/f'{n}.olean';need(H(ROOT/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and H(obj)==r['object_sha256'],'source/object')
for k in ('deps','compile'):need(H(ROOT/f'{n}-{k}.txt')==r[k]['log_sha256'],'log '+k)
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:need(not os.path.lexists(q),'unexpected '+path)
 else:need(q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256'],'guard '+path)
q=BASE/'lib/DiophantineConsistency'/f'{n}.olean';need(q.is_file() and q.resolve()==obj.resolve() and H(q)==r['object_sha256'],'overlay route')
draft=D/'research/nine-sharing-sign25-octic-lean-draft/SharingSeed25BridgeDraft.lean';need(H(draft)=='62a6a45b6b1aa669282da1823d2757aa031dae02767159d966da989de702faa1','bridge draft pin');src=(P/'src/DiophantineConsistency/Sign25CoordinateDrop.lean').read_text();need(src.split('def drop ',1)[1].split('\n\n',1)[0]==draft.read_text().split('def drop ',1)[1].split('\n\n',1)[0],'drop definition mismatch')
print(json.dumps({'status':'PASS','first_cut_sha256':r['object_sha256'],'scope':'first-cut producer/guard and drop source; deeper ancestry inherited'},sort_keys=True))
