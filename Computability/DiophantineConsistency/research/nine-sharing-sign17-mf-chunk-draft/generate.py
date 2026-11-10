#!/usr/bin/env python3
"""Generate SOURCE-ONLY MF digit/byte chunk identities from frozen bytes."""
import gzip,hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
here=Path(__file__).resolve().parent;seed=here.parent/'nine-sharing-sign17-degree96-vdifference-candidate/seed.json';sha=lambda b:hashlib.sha256(b).hexdigest();text=seed.read_bytes();assert sha(text)=='0323ee371aac07604617495952c6a5e0b7ead5e66697a485a05358fb447689ac';binding=json.loads(text)['coefficient_binding'];record=binding['ports']['MF'];packed=(seed.parent/binding['path']/record['file']).read_bytes();raw=gzip.decompress(packed);assert sha(packed)==record['gzip_sha256'] and sha(raw)==record['raw_sha256'] and len(raw)==11815
little=raw[::-1];digits=[3]+[8]*916+[0]*43+[1]*9+[0]*18+[1]*8+[0]*9+[1,2**45-4]+[0]*1005+[1];assert len(digits)==2012
cases=[('first',0,8),('eights',1,8),('end_eights',114,8),('zeros',115,8),('ones',120,8),('end_ones',121,8),('start_ones',123,8),('end_ones2',124,8),('marker',125,8),('tail',251,4)]
lines=['import DiophantineConsistency.Sign17ExactDegree\n','/-! SOURCE-ONLY: MF radix/byte chunk identities; file provenance is external. -/\n','set_option autoImplicit false\nnoncomputable section\nnamespace DiophantineConsistency.Sign17MFChunks\n'];results=[];radix=2**47
for name,i,count in cases:
 d=digits[i*8:i*8+count];chunk=little[47*i:47*(i+1)];assert len(d)==count and len(chunk)==(47 if count==8 else 18);assert int.from_bytes(chunk,'little')==sum(x*radix**j for j,x in enumerate(d));ds=', '.join('(2 ^ 45 - 4)' if x==2**45-4 else str(x) for x in d);bs=', '.join(str(x) for x in chunk);lines.append(f'\ntheorem {name} :\n    Nat.ofDigits CurrentMasks2011.radix [{ds}] =\n      Nat.ofDigits 256 [{bs}] := by\n  unfold CurrentMasks2011.radix\n  decide +kernel\n');results.append({'name':name,'block_index':i,'radix_digits':count,'byte_count':len(chunk),'byte_sha256':sha(chunk)})
lines.append('\nend DiophantineConsistency.Sign17MFChunks\n');lines.extend(f'#print axioms DiophantineConsistency.Sign17MFChunks.{name}\n' for name,_,_ in cases);source=''.join(lines);out=here/'Sign17MFChunks.lean'
if out.exists():raise SystemExit('refusing overwrite')
out.write_text(source);print(json.dumps({'status':'GENERATED_SOURCE_ONLY','source_sha256':sha(source.encode()),'chunks':results,'scope':'External fixture extraction, no Lean theorem or full binding.'},indent=2,sort_keys=True))
