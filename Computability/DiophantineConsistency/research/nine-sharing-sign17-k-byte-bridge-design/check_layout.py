#!/usr/bin/env python3
"""External check of proposed K radix-digit layout; not a Lean/file theorem."""
from pathlib import Path
import gzip,hashlib,json,sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
here=Path(__file__).resolve().parent;cp=here.parent/'padding-staircase-independent/coefficients.json';seed=here.parent/'nine-sharing-sign17-degree96-vdifference-candidate/seed.json';h=lambda b:hashlib.sha256(b).hexdigest();cb=cp.read_bytes();sb=seed.read_bytes();assert h(cb)=='43f31dd15eb258cca8979aaf39ea8987df9ac573246e50f94bd43769c470dc93';assert h(sb)=='0323ee371aac07604617495952c6a5e0b7ead5e66697a485a05358fb447689ac';c=json.loads(cb);assert len(c)==3297 and all(x==0 for x in c[986:]);r=2**47
d=[0]*18+[1,0]+list(reversed(c[:986]))+[0]*1014+[1];assert len(d)==2021;d[1004]+=1;assert all(0<=x<r for x in d)
binding=json.loads(sb)['coefficient_binding'];rec=binding['ports']['K0'];packed=(seed.parent/binding['path']/rec['file']).read_bytes();raw=gzip.decompress(packed);assert h(packed)==rec['gzip_sha256'] and h(raw)==rec['raw_sha256'];v=0
for x in reversed(d):v=v*r+x
assert v==int.from_bytes(raw,'big')
print(json.dumps({'status':'PASS_EXTERNAL_K_DIGIT_LAYOUT','coefficient_sha256':h(cb),'seed_sha256':h(sb),'raw_sha256':h(raw),'digit_count':len(d),'sentinel_collision_index':1004,'scope':'External Python snapshot check; not a Lean digit, JSON or file theorem.'},sort_keys=True,indent=2))
