#!/usr/bin/env python3
"""Authenticate the transitive first-cut object used directly by bridge terms."""
import hashlib,json,os
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1];ROOT=Path('/tmp/nine-sharing-sign31-first-cut-check-20261106');BASE=Path('/tmp/nine-sharing-sign31-remaining-cuts-check-20261106');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,m):
 if not v:raise RuntimeError(m)
p=D/'research/nine-sharing-sign31-first-cut-check/attempt01';need(H(p/'state.json')=='585e83086a5c4c29e5d8fdfbada9231fc4f8b1e2a1df5bfc2972cd74bad57131' and H(p/'outer-result.json')=='a1d181e8a8fcbd54f6e821c78feb51ad4e369bd2250f490b0c9c05df797fc15a','receipt pins');d=json.loads((p/'state.json').read_text());o=json.loads((p/'outer-result.json').read_text());need(d['status']=='PASS' and len(d['rows'])==1 and o['author_observed_numeric_outer_exit']==0,'producer status');r=d['rows'][0];n='Sign31FirstCut';need(r['module']==n and r['deps']['exit']==0 and r['compile']['exit']==0,'row');obj=ROOT/'lib/DiophantineConsistency'/f'{n}.olean';need(H(ROOT/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and H(obj)==r['object_sha256'],'source/object')
for k in ('deps','compile'):need(H(ROOT/f'{n}-{k}.txt')==r[k]['log_sha256'],'log '+k)
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:need(not os.path.lexists(q),'unexpected '+path)
 else:need(q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256'],'guard '+path)
q=BASE/'lib/DiophantineConsistency'/f'{n}.olean';need(q.is_file() and q.resolve()==obj.resolve() and H(q)==r['object_sha256'],'overlay route')
draft=D/'research/nine-sharing-sign31-sextic-lean-draft/SharingSeed31BridgeDraft.lean';need(H(draft)=='0e3bbc84ee88879183619bbe283321f651621345a9c4deab3febe903aaa21ad3','bridge draft pin');src=(P/'src/DiophantineConsistency/Sign31CoordinateDrop.lean').read_text();need(src.split('def drop ',1)[1].split('\n\n',1)[0]==draft.read_text().split('def drop ',1)[1].split('\n\n',1)[0],'drop definition mismatch')
print(json.dumps({'status':'PASS','first_cut_sha256':r['object_sha256'],'scope':'first-cut producer/guard and drop source; deeper ancestry inherited'},sort_keys=True))
