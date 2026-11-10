#!/usr/bin/env python3
"""Authenticate three bypass producers and byte-match their overlay unions."""
import hashlib,json,os
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1];BASE=Path('/tmp/nine-sharing-sign24-expression-equivalence-check-20261109');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,m):
 if not v:raise RuntimeError(m)
u=json.loads((P/'union.json').read_text());result={}
for name,root,statepin,outerpin,module,packetrel in (
 ('generic','/tmp/nine-sharing-generic-polynomial-bridge-transport-retry01-20261106','4751cdfc27a4f72a533f11c0b83b0db02acf6a14e2bff36186dc307ceffaa111','ef35dae8397f85cd90489ae06fa4d91966d08bf7c787d94425f3638cd1948b5f','GenericPolynomialBridgeTransport','research/nine-sharing-generic-polynomial-bridge-transport-retry01/attempt01'),
 ('sign25iff','/tmp/nine-sharing-sign25-expression-equivalence-check-20261106','fed307cd8b6e8aeae4740b47cb3d68fbc5b3dbc99d166fe82be6a977a61167ed','7f52bc1a5dcab605e1daa106195b979c1aa803cfccca39bbd73e3086ec4bae5b','Sign25ExpressionEquivalence','research/nine-sharing-sign25-expression-equivalence-check/attempt01'),
 ('sign26bridge','/tmp/nine-sharing-sign26-concrete-polynomial-bridge-check-20261106','17330cbc2d93f3acf758b96ade59604a05ee5473de35b347905c942a49e978b6','c9d2482a0cc09ac1680265feb5343c430e88c41ca11c30ee47a9e1bb218bc0b2','Sign26DirectPolynomialBridge','research/nine-sharing-sign26-concrete-polynomial-bridge-check/attempt01'),
):
 root=Path(root);packet=D/packetrel;need(H(packet/'state.json')==statepin and H(packet/'outer-result.json')==outerpin,'receipt '+name);d=json.loads((packet/'state.json').read_text());o=json.loads((packet/'outer-result.json').read_text());need(d['status']=='PASS' and o['author_observed_numeric_outer_exit']==0,'status '+name)
 rows=[r for r in d['rows'] if r['module']==module];need(len(rows)==1,'row '+name);r=rows[0];need(r['deps']['exit']==0 and r['compile']['exit']==0,'stage '+name);obj=root/'lib/DiophantineConsistency'/f'{module}.olean';need(H(root/'src/DiophantineConsistency'/f'{module}.lean')==r['source_sha256'] and H(obj)==r['object_sha256'],'source/object '+name)
 for k in ('deps','compile'):need(H(root/f'{module}-{k}.txt')==r[k]['log_sha256'],'log '+name)
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:need(not os.path.lexists(q),'unexpected '+path)
  else:need(q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256'],'guard '+path)
 for x in (BASE/'lib',Path('/tmp/current2011-spheres-fresh-base-priority-check02'),Path('/tmp/normalized106-fresh-model-client-20261105'),Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'),Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')):need(not os.path.lexists(x/'DiophantineConsistency'/f'{module}.olean'),'module collision '+name)
 over=0;extra={}
 for path,target in d['overlay_links'].items():
  q=Path(path);need(q.is_symlink() and str(q.resolve())==target,'overlay '+path);rel=str(q.relative_to(root/'lib'));bq=BASE/'lib'/rel
  if bq.is_file():need(H(bq)==H(q),'overlay bytes '+rel);over+=1
  else:extra[rel]={'realpath':str(q.resolve()),'sha256':H(q)}
 need(over==u[name]['overlap_count'] and extra==u[name]['extra'],'union '+name)
 for rel in extra:
  for x in (Path('/tmp/current2011-spheres-fresh-base-priority-check02'),Path('/tmp/normalized106-fresh-model-client-20261105'),Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'),Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')):need(not os.path.lexists(x/rel),'fallback collision '+rel)
 result[name]={'object_sha256':r['object_sha256'],'object_realpath':str(obj.resolve()),'overlap_count':over,'extra_count':len(extra)}
print(json.dumps({'status':'PASS','producers':result,'scope':'three successful bypass provider rows and byte-matched overlays; deeper ancestry inherited'},sort_keys=True))
