#!/usr/bin/env python3
"""Authenticate five field producers and selected assembly routes; no Lean."""
import hashlib,json,os,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];BASE=Path('/tmp/nine-sharing-norm38-reference-z-factored-check-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
items=[('fields01','Norm38ReferenceFields01','395733ddb717547637718bdc8914a86e94d19e2798148c3d7bf4b4df73c9b292','032511edc32be5e4e4cf9ee6a3a610ce0220a71a634b8f345615263b43c17fce'),('w','Norm38ReferenceW','4850cac5e7763883617255c554d743e82a0c91a6f07f2b69d63432ff07b75a96','113d3d8021fe7b40ca19f7fca5eedbecf0b8ae87af6ab5d2de188f777775cbdb'),('delta','Norm38ReferenceDelta','3f4fd6ae49b2a4a3da22e07849205f55ca9012bb14c2ee8c09297907d598aa2b','d43d2cbdd4e19edad31de95b48e51ba1459a4cdc61a286e742d8279e01292a65'),('u-factored','Norm38ReferenceUFactored','4fba8a5d941e00d22e0a43f3ef34a83fb3e69ac59755f6a7602989d30c5630f8','a0525e2c12c72839474fdfc5562cb3bf723218768616efd7808154866075e42f'),('z-factored','Norm38ReferenceZFactored','601a5b75826f06da85743490792dc8816d2c56f8b0a33de669544732c86015e2','a64a0e35d5903db00af87f502a074f8ecb669c9a784bd1464a110e59fc20c89c')]
guards=0
for tag,n,sp,op in items:
 packet=D/'research'/('nine-sharing-norm38-reference-'+tag+'-check');t=Path('/tmp/nine-sharing-norm38-reference-'+tag+'-check-20261105');need(sha(packet/'attempt01/state.json')==sha(t/'state.json')==sp,'state '+n);s=json.loads((packet/'attempt01/state.json').read_text());need(s['status']=='PASS' and len(s['rows'])==1,'status '+n);r=s['rows'][0];need(r['module']==n and r['deps']['exit']==0 and r['compile']['exit']==0 and r['compile']['stop_reason'] is None and sha(t/'src/DiophantineConsistency'/(n+'.lean'))==r['source_sha256'] and sha(t/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256']==op,'source/object '+n)
 for k in ('deps','compile'):need(sha(t/(n+'-'+k+'.txt'))==sha(packet/'attempt01'/(n+'-'+k+'.txt'))==r[k]['log_sha256'],'log '+n+k)
 for path,v in r['direct_guard'].items():
  guards+=1;q=Path(path)
  if v is None:need(not os.path.lexists(q),'unexpected '+path)
  else:need(q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],'guard '+path)
 target=BASE/'lib/DiophantineConsistency'/(n+'.olean')
 if tag in ('fields01','w'):need(not os.path.lexists(target),'injection target collision '+n)
 else:need(target.is_file() and target.resolve()==(t/'lib/DiophantineConsistency'/(n+'.olean')).resolve() and sha(target)==op,'provider route '+n)
for n in ('Norm38ReferenceFieldsAll','Norm38StaticCarrierConditional'):need(not os.path.lexists(BASE/'lib/DiophantineConsistency'/(n+'.olean')),'output collision '+n)
print(json.dumps({'status':'PASS_FIVE_FIELD_PRODUCER_SURVEY','producer_count':len(items),'recorded_direct_guard_slots':guards,'scope':'Five successful producer records and selected overlay routes; no Lean and no complete dynamic/transitive ancestry.'},sort_keys=True,indent=2))
