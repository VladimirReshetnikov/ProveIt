#!/usr/bin/env python3
"""Authenticate gap provider and byte-match its overlay with zero assembly."""
import hashlib,json,os
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1];BASE=Path('/tmp/nine-sharing-sign17-zero-assembly-check-20261109');ROOT=Path('/tmp/nine-sharing-sign17-gap-from-seed-20261110');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,m):
 if not v:raise RuntimeError(m)
packet=D/'research/nine-sharing-sign17-gap-from-seed-check/attempt01';need(H(packet/'state.json')=='442aeecc5fc3b1bdd175b24f19f11642ed794a437582441d624aa419807f4f15' and H(packet/'outer-result.json')=='0929dade886efb87f036aa417624057e138d683a5756b0f9a0c7d94f1fda9f65','gap receipts');need(H(D/'reviews/nine-sharing-sign17-gap-from-seed-terminal-independent/check.py')=='007efbea6bc45b7b4fba6435c85837c18674b7ed1374e2d9503ec5deb17d580a','gap terminal audit pin');d=json.loads((packet/'state.json').read_text());o=json.loads((packet/'outer-result.json').read_text());need(d['status']=='PASS' and o['outer_exit_code']==0 and len(d['rows'])==1,'gap status');row=d['rows'][0];name='Sign17GapFromSeed';need(row['module']==name and row['deps']['exit']==0 and row['compile']['exit']==0,'gap row');obj=ROOT/'lib/DiophantineConsistency'/f'{name}.olean';need(H(ROOT/'src/DiophantineConsistency'/f'{name}.lean')==row['source_sha256'] and H(obj)==row['object_sha256'],'gap source/object')
for k in ('deps','compile'):need(H(ROOT/f'{name}-{k}.txt')==row[k]['log_sha256'],'gap log '+k)
for path,v in row['direct_guard'].items():
 q=Path(path)
 if v is None:need(not os.path.lexists(q),'unexpected '+path)
 else:need(q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256'],'guard '+path)
over=0;extra={}
for path,target in d['overlay_links'].items():
 q=Path(path);need(q.is_symlink() and str(q.resolve())==target,'overlay '+path);rel=str(q.relative_to(ROOT/'lib'));bq=BASE/'lib'/rel
 if bq.is_file():need(H(bq)==H(q),'overlap '+rel);over+=1
 else:extra[rel]={'realpath':str(q.resolve()),'sha256':H(q)}
u=json.loads((P/'union.json').read_text())['gap'];need(over==u['overlap_count'] and extra==u['extra'],'union')
for rel in list(extra)+['DiophantineConsistency/Sign17GapFromSeed.olean']:
 for x in (Path('/tmp/current2011-spheres-fresh-base-priority-check02'),Path('/tmp/normalized106-fresh-model-client-20261105'),Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'),Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')):need(not os.path.lexists(x/rel),'fallback collision '+rel)
need(not os.path.lexists(BASE/'lib/DiophantineConsistency/Sign17GapFromSeed.olean'),'base collision gap')
print(json.dumps({'status':'PASS','producers':{'gap':{'object_sha256':row['object_sha256'],'object_realpath':str(obj.resolve()),'overlap_count':over,'extra_count':len(extra)}},'scope':'audited gap producer and byte-matched overlay; deeper ancestry inherited'},sort_keys=True))
