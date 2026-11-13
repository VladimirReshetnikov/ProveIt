#!/usr/bin/env python3
"""External decomposition of frozen K coefficient recipe into aligned byte blocks."""
import gzip,hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
here=Path(__file__).resolve().parent;seed=here.parent/'nine-sharing-sign17-degree96-vdifference-candidate/seed.json';coeffs=here.parent/'padding-staircase-independent/coefficients.json';sha=lambda b:hashlib.sha256(b).hexdigest();text=seed.read_bytes();assert sha(text)=='0323ee371aac07604617495952c6a5e0b7ead5e66697a485a05358fb447689ac';cb=coeffs.read_bytes();assert sha(cb)=='43f31dd15eb258cca8979aaf39ea8987df9ac573246e50f94bd43769c470dc93';c=json.loads(cb);assert len(c)==3297 and max(i for i,x in enumerate(c) if x)==985
binding=json.loads(text)['coefficient_binding'];rec=binding['ports']['K0'];packed=(seed.parent/binding['path']/rec['file']).read_bytes();raw=gzip.decompress(packed);assert sha(packed)==rec['gzip_sha256'] and sha(raw)==rec['raw_sha256'] and len(raw)==11868
radix=2**47;digits=[0]*2021
for i,x in enumerate(c):
 if x:digits[1005-i]+=x
for j in (18,1004,2020):digits[j]+=1
assert all(0<=x<radix for x in digits)
little=raw[::-1];blocks=[little[i:i+47] for i in range(0,len(little),47)];assert len(blocks)==253 and len(blocks[-1])==24
for i,b in enumerate(blocks):
 ds=digits[8*i:min(8*i+8,len(digits))];assert int.from_bytes(b,'little')==sum(x*radix**j for j,x in enumerate(ds))
assert int.from_bytes(raw,'big')==sum(x*radix**i for i,x in enumerate(digits))
print(json.dumps({'status':'PASS_EXTERNAL_K_BLOCK_LAYOUT','seed_sha256':sha(text),'coefficient_array_sha256':sha(cb),'raw_sha256':sha(raw),'raw_bytes':len(raw),'radix_digits':len(digits),'blocks':len(blocks),'distinct_byte_patterns':len(set(blocks)),'zero_full_blocks':sum(b==bytes(47) for b in blocks),'tail_bytes':len(blocks[-1]),'block_sha256':[sha(b) for b in blocks], 'scope':'External coefficient-array/byte decomposition only; no Lean K-to-array, gzip or file theorem.'},indent=2,sort_keys=True))
