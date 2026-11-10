#!/usr/bin/env python3
"""External check of pinned K bytes against the frozen coefficient recipe."""
import gzip, hashlib, json, sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
here=Path(__file__).resolve().parent
seed=here.parent/'nine-sharing-sign17-degree96-vdifference-candidate/seed.json'
coeffs=here.parent/'padding-staircase-independent/coefficients.json'
sha=lambda b:hashlib.sha256(b).hexdigest()
text=seed.read_bytes(); assert sha(text)=='0323ee371aac07604617495952c6a5e0b7ead5e66697a485a05358fb447689ac'
cbytes=coeffs.read_bytes(); assert sha(cbytes)=='43f31dd15eb258cca8979aaf39ea8987df9ac573246e50f94bd43769c470dc93'
c=json.loads(cbytes);assert len(c)==3297 and all(isinstance(x,int) and x>=0 for x in c)
assert max(i for i,x in enumerate(c) if x)==985
binding=json.loads(text)['coefficient_binding'];rec=binding['ports']['K0']
packed=(seed.parent/binding['path']/rec['file']).read_bytes();raw=gzip.decompress(packed)
assert sha(packed)==rec['gzip_sha256'] and sha(raw)==rec['raw_sha256'] and len(raw)==rec['raw_bytes']==11868
r=2**47
value=r**18+r**1004+r**2020+sum(x*r**(1005-i) for i,x in enumerate(c) if x)
assert value==int.from_bytes(raw,'big')
print(json.dumps({'status':'PASS_EXTERNAL_K_COEFFICIENT_RECIPE','seed_sha256':sha(text),
 'coefficient_array_sha256':sha(cbytes),'coefficient_count':len(c),'last_nonzero_index':985,
 'gzip_sha256':sha(packed),'raw_sha256':sha(raw),'raw_bytes':len(raw),
 'scope':'External Python coefficient-recipe check; not a Lean K/byte or file theorem.'},sort_keys=True,indent=2))
