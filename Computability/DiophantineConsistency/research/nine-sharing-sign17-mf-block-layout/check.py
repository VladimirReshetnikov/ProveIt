#!/usr/bin/env python3
"""External reconstruction of pinned MF source bytes from radix/byte blocks."""
import gzip,hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
here=Path(__file__).resolve().parent;seed=here.parent/'nine-sharing-sign17-degree96-vdifference-candidate/seed.json';sha=lambda b:hashlib.sha256(b).hexdigest();text=seed.read_bytes();assert sha(text)=='0323ee371aac07604617495952c6a5e0b7ead5e66697a485a05358fb447689ac';binding=json.loads(text)['coefficient_binding'];r=binding['ports']['MF'];packed=(seed.parent/binding['path']/r['file']).read_bytes();raw=gzip.decompress(packed);assert sha(packed)==r['gzip_sha256'] and sha(raw)==r['raw_sha256'] and len(raw)==11815
little=raw[::-1];digits=[3]+[8]*916+[0]*43+[1]*9+[0]*18+[1]*8+[0]*9+[1,2**45-4]+[0]*1005+[1];assert len(digits)==2012
indices={'first':0,'eights':1,'end_eights':114,'zeros':115,'ones':120,'end_ones':121,'start_ones':123,'end_ones2':124,'marker':125,'tail':251}
fixtures={k:little[47*i:47*(i+1)] for k,i in indices.items()};patterns={k:digits[8*i:8*i+(4 if k=='tail' else 8)] for k,i in indices.items()}
segments=[('first',1),('eights',113),('end_eights',1),('zeros',5),('ones',1),('end_ones',1),('zeros',1),('start_ones',1),('end_ones2',1),('marker',1),('zeros',125),('tail',1)]
assert sum(n for _,n in segments)==252
assert b''.join(fixtures[k]*n for k,n in segments)==little
assert sum((patterns[k]*n for k,n in segments),[])==digits
for k,block in fixtures.items():assert int.from_bytes(block,'little')==sum(x*(2**47)**i for i,x in enumerate(patterns[k]))
print(json.dumps({'status':'PASS_EXTERNAL_MF_BLOCK_LAYOUT','seed_sha256':sha(text),'raw_sha256':sha(raw),'raw_bytes':len(raw),'blocks':252,'segments':segments,'radix_digits':len(digits),'fixture_sha256':{k:sha(v) for k,v in fixtures.items()},'scope':'External Python reconstruction only; no Lean whole-port or file theorem.'},sort_keys=True,indent=2))
