#!/usr/bin/env python3
"""Point-in-time guard survey for the separate field/conditional producer chain."""
import hashlib,json,os,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];BASE=Path('/tmp/nine-sharing-norm38-reference-terminals-check-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
items=[('static-carrier-retry02','Norm38StaticCarrierConditional','77cba4b06bb6921bccb517e135d94b5b54dc0d25f602774b9d23be9d15c28951','7d0b8cbb7cd6a01447ff710deb1f22336c3765bc4e7b5149b9cc3424eef491f6'),('reference-fields-combine-check','Norm38ReferenceFieldsAll','7bd683c7d990981e7b1172c16c73c294a4da4f88382949da0d88158c5c580fbc','3f7e3aea0ca0fa2c9700d128fd6d3a563a2345a0d61b81bcd0d87478c98b2dfd'),('reference-fields01-check','Norm38ReferenceFields01','395733ddb717547637718bdc8914a86e94d19e2798148c3d7bf4b4df73c9b292','032511edc32be5e4e4cf9ee6a3a610ce0220a71a634b8f345615263b43c17fce'),('reference-w-check','Norm38ReferenceW','4850cac5e7763883617255c554d743e82a0c91a6f07f2b69d63432ff07b75a96','113d3d8021fe7b40ca19f7fca5eedbecf0b8ae87af6ab5d2de188f777775cbdb'),('reference-delta-check','Norm38ReferenceDelta','3f4fd6ae49b2a4a3da22e07849205f55ca9012bb14c2ee8c09297907d598aa2b','d43d2cbdd4e19edad31de95b48e51ba1459a4cdc61a286e742d8279e01292a65'),('reference-u-factored-check','Norm38ReferenceUFactored','4fba8a5d941e00d22e0a43f3ef34a83fb3e69ac59755f6a7602989d30c5630f8','a0525e2c12c72839474fdfc5562cb3bf723218768616efd7808154866075e42f'),('reference-z-factored-check','Norm38ReferenceZFactored','601a5b75826f06da85743490792dc8816d2c56f8b0a33de669544732c86015e2','a64a0e35d5903db00af87f502a074f8ecb669c9a784bd1464a110e59fc20c89c'),('reference-u-edges-retry01','Norm38ReferenceUEdges','dbe89b1dd4d849a60008700d2d0274b227658643a3d8441c2159e4ae7e843290','7cb827b6b2ef7d5fb503106f7861daa2c8553a00823c798c18f63d2236421fdd')]
guards=0
for tag,n,sp,op in items:
 packet=D/'research'/('nine-sharing-norm38-'+tag)/'attempt01';t=Path('/tmp/nine-sharing-norm38-'+tag+'-20261105');need(sha(packet/'state.json')==sha(t/'state.json')==sp,'state '+n);s=json.loads((packet/'state.json').read_text());need((s['status']=='FAILED' and len(s['rows'])==2 and s['rows'][1]['compile']['exit']==1) if tag=='reference-fields-combine-check' else (s['status']=='PASS' and len(s['rows'])==1),'state status '+n);r=s['rows'][0];need(r['module']==n and all(r[k]['exit']==0 and r[k]['stop_reason'] is None for k in ('deps','compile')) and sha(t/'src/DiophantineConsistency'/(n+'.lean'))==r['source_sha256'] and sha(t/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256']==op,'source/object '+n)
 for k in ('deps','compile'):need(sha(t/(n+'-'+k+'.txt'))==sha(packet/(n+'-'+k+'.txt'))==r[k]['log_sha256'],'log '+n+k)
 for path,v in r['direct_guard'].items():
  guards+=1;q=Path(path)
  if v is None:need(not os.path.lexists(q),'unexpected '+path)
  else:need(q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],'guard '+path)
 need(not os.path.lexists(BASE/'lib/DiophantineConsistency'/(n+'.olean')),'injection collision '+n)
need(not os.path.lexists(BASE/'lib/DiophantineConsistency/Norm38StaticCarrierCompose.olean'),'target collision')
print(json.dumps({'status':'PASS_STATIC_CARRIER_PRODUCER_SURVEY','producers':len(items),'direct_guard_slots':guards,'scope':'Selected successful producer records and overlay-collision point checks; initial agreement outer exit was not captured; no Lean or full dynamic ancestry.'},sort_keys=True,indent=2))
