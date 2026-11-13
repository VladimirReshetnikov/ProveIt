#!/usr/bin/env python3
"""External check: reconstruct pinned MC raw bytes and radix digits by chunk runs."""
import gzip, hashlib, json, sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
here=Path(__file__).resolve().parent
seed=here.parent/'nine-sharing-sign17-degree96-vdifference-candidate/seed.json'
sha=lambda b:hashlib.sha256(b).hexdigest()
text=seed.read_bytes();assert sha(text)=='0323ee371aac07604617495952c6a5e0b7ead5e66697a485a05358fb447689ac'
binding=json.loads(text)['coefficient_binding'];record=binding['ports']['MC']
packed=(seed.parent/binding['path']/record['file']).read_bytes();raw=gzip.decompress(packed)
assert sha(packed)==record['gzip_sha256'] and sha(raw)==record['raw_sha256'] and len(raw)==11815
little=raw[::-1]
case_indices={'all_selected':0,'boundary_951':118,'all_unselected':119,'boundary_986':123,'marker_1004':125,'final_3':251}
fixtures={name:little[47*i:47*(i+1)] for name,i in case_indices.items()}
segments=[('all_selected',118),('boundary_951',1),('all_unselected',1),('all_selected',3),
          ('boundary_986',1),('all_unselected',1),('marker_1004',1),('all_unselected',125),('final_3',1)]
reconstructed=b''.join(fixtures[name]*count for name,count in segments)
assert reconstructed==little and sum(n for _,n in segments)==252
r=2**47; chosen=r-2; other=r-1
runs=[chosen]*951+[other]*9+[chosen]*26+[other]*18+[chosen]+[other]*1006
patterns={'all_selected':[chosen]*8,'boundary_951':[chosen]*7+[other],
          'all_unselected':[other]*8,'boundary_986':[chosen]*2+[other]*6,
          'marker_1004':[other]*4+[chosen]+[other]*3,'final_3':[other]*3}
digits=sum((patterns[name]*count for name,count in segments),[])
assert digits==runs and len(digits)==2011
for name,chunk in fixtures.items():
    assert int.from_bytes(chunk,'little')==sum(x*r**i for i,x in enumerate(patterns[name]))
print(json.dumps({'status':'PASS_EXTERNAL_BLOCK_LAYOUT','seed_sha256':sha(text),'raw_sha256':sha(raw),
 'raw_bytes':len(raw),'blocks':252,'segments':segments,'radix_digits':len(digits),
 'fixture_sha256':{name:sha(chunk) for name,chunk in fixtures.items()},
 'scope':'External Python reconstruction only; no Lean whole-port or file theorem.'},indent=2,sort_keys=True))
