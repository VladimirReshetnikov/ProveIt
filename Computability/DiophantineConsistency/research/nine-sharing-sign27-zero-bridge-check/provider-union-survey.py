#!/usr/bin/env python3
"""Authenticate two bridge producers and byte-match their overlay unions."""
import hashlib,json,os
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1];BASE=Path('/tmp/nine-sharing-sign27-remaining-cuts-check-20261106');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,m):
 if not v:raise RuntimeError(m)
u=json.loads((P/'union.json').read_text());result={}
for name,root,statepin,outerpin,module,packetrel in (
 ('affected','/tmp/nine-sharing-sign27-affected-cuts-check-20261106','0402805f20ab4ba4d22ba3271aac0adff00cd236992f1aba8aa52ff6a49bbd9a','6566e4c2172bb4ae7ae1ed8b886ddeea54f419a6490ae05ac9509c300c9a9cac','Sign27AffectedCuts','research/nine-sharing-sign27-affected-cuts-check/attempt01'),
 ('seedroot','/tmp/nine-sharing-sign27-seed-root-recovery-check-20261106','2d16a4676ee192bd1b57aeaec13c0fc126f31d0a8bb5031423dfdb287c83fbe2','ac7a98ff9865662aeffcf21a35d418bb52a3e9b7fa2eced9f731bf2f3fba7e1e','Sign27SeedRootRecovery','research/nine-sharing-sign27-seed-root-recovery-check/attempt01'),
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
print(json.dumps({'status':'PASS','producers':result,'scope':'two successful sign27 provider rows and byte-matched overlays; deeper ancestry inherited'},sort_keys=True))
