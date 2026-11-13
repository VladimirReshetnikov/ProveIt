#!/usr/bin/env python3
"""Point-in-time P72 and sign33 overlay comparison, with direct guard checks."""
import hashlib, json, os, sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
D = Path(__file__).resolve().parent.parent
p72 = Path('/tmp/p72-current-base-extension-attempt02-20261105')
progress = D / 'p72-current-base-extension-build-attempt02/terminal/progress.json'
assert sha(progress) == 'f4bbe5f0b543497d543f243e10d8ead6d778cc3d0bf0aec96dfa73f7e622dd5a'
assert json.loads(progress.read_text())['status'] == 'PASS'
auxpath=p72/'rows/0620.json';assert sha(auxpath)=='2d2dffed0e1f504776b017a37c91d42b0973eb613d18b54c9d0a6a9c60bdab60'
aux=json.loads(auxpath.read_text());half=aux['dependencies']['DiophantineConsistency.ArithmeticPellHalfIndex']
assert half['sha256']=='6142ab8eaac6e281c3372817a6f1a8cbc14704717d4f5479c28603c754c3a4d7'==sha(half['realpath'])
slots=0
for idx,name in [('0618','DiophantineConsistency.Compact44.P72Root'),('0619','DiophantineConsistency.Compact44.P72Main'),('0620','DiophantineConsistency.Compact44.P72Aux')]:
 row=json.loads((p72/'rows'/f'{idx}.json').read_text());assert row['module']==name and row['status']=='PASS'
 for k,v in row['direct_guard'].items():
  slots+=1;p=Path(k)
  if v is None: assert not os.path.lexists(p)
  else: assert p.is_file() and str(p.resolve())==v['realpath'] and sha(p)==v['sha256']
 for v in row['dependencies'].values():
  p=Path(v['path']);assert p.is_file() and str(p.resolve())==v['realpath'] and sha(p)==v['sha256']
sign=D/'nine-sharing-sign33-inner-v-ring-check/attempt01/survey-before.json';assert sha(sign)=='d9f974099b02b4f95706040bef7499ec35c7f8757bf7629c811b2b547259ff7f';s=json.loads(sign.read_text());assert s['status']=='PASS_POINT_PRODUCER_SURVEY'
overlap=0;diff=[]
for rel,record in s['links'].items():
 q=p72/'lib'/rel
 if q.is_file():
  overlap+=1;h=sha(q)
  if h!=record['sha256']:diff.append({'path':rel,'sign33_sha256':record['sha256'],'p72_sha256':h})
assert overlap==1007 and len(diff)==1 and diff[0]['path']=='DiophantineConsistency/ModelDifferenceRing.olean'
assert diff[0]['sign33_sha256']=='cf2b32cb1e4777b7cff73c34ed7334a105f705912fa987e9f7f9a316fef192f0'
assert diff[0]['p72_sha256']=='e52ed546fa3f94d9c3b823ad19286c4c906359efa26c1d67543e9dbfc0f2ecf0'
print(json.dumps({'status':'PASS_OVERLAY_COMPARISON','half_index_sha256':half['sha256'],'direct_guard_slots_checked':slots,'overlap_count':overlap,'differences':diff,'scope':'Point-in-time comparison only; no proof of incompatibility or of complete transitive/dynamic ancestry.'},indent=2,sort_keys=True))
