#!/usr/bin/env python3
"""Generate six SOURCE-ONLY MC little-endian chunk fixtures from frozen bytes."""
import gzip, hashlib, json, sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
here=Path(__file__).resolve().parent
seed=here.parent/'nine-sharing-sign17-degree96-vdifference-candidate/seed.json'
sha=lambda b:hashlib.sha256(b).hexdigest()
text=seed.read_bytes(); assert sha(text)=='0323ee371aac07604617495952c6a5e0b7ead5e66697a485a05358fb447689ac'
binding=json.loads(text)['coefficient_binding']; record=binding['ports']['MC']
packed=(seed.parent/binding['path']/record['file']).read_bytes(); raw=gzip.decompress(packed)
assert sha(packed)==record['gzip_sha256'] and sha(raw)==record['raw_sha256'] and len(raw)==11815
little=raw[::-1]; support=set(range(951))|set(range(960,986))|{1004}; radix=2**47
cases=[('all_selected',0,8),('boundary_951',118,8),('all_unselected',119,8),
       ('boundary_986',123,8),('marker_1004',125,8),('final_3',251,3)]
lines=['import DiophantineConsistency.Sign17ExactDegree\n',
       '/-! SOURCE-ONLY: six MC radix/byte block identities; file binding is external. -/\n',
       'set_option autoImplicit false\nnoncomputable section\n',
       'namespace DiophantineConsistency.Sign17MCChunks\n']
results=[]
for name,index,count in cases:
    chunk=little[47*index:47*(index+1)]; digs=[radix-(2 if j in support else 1) for j in range(8*index,8*index+count)]
    assert len(chunk)==(47 if count==8 else 18)
    value=sum(x*radix**i for i,x in enumerate(digs)); assert value==int.from_bytes(chunk,'little')
    offsets=[2 if j in support else 1 for j in range(8*index,8*index+count)]
    ds=', '.join('CurrentMasks2011.radix - '+str(x) for x in offsets)
    bs=', '.join(str(x) for x in chunk)
    lines.append(f'\ntheorem {name} :\n    Nat.ofDigits CurrentMasks2011.radix [{ds}] =\n      Nat.ofDigits 256 [{bs}] := by\n  unfold CurrentMasks2011.radix\n  decide +kernel\n')
    results.append({'name':name,'block_index':index,'radix_digits':count,'byte_count':len(chunk),'byte_sha256':sha(chunk)})
lines.append('\nend DiophantineConsistency.Sign17MCChunks\n')
for name,_,_ in cases:lines.append(f'#print axioms DiophantineConsistency.Sign17MCChunks.{name}\n')
source=''.join(lines);out=here/'Sign17MCChunks.lean'
if out.exists():raise SystemExit('refusing overwrite')
out.write_text(source)
print(json.dumps({'status':'GENERATED_SOURCE_ONLY','source_sha256':sha(source.encode()),'chunks':results,
  'scope':'External fixture extraction; no Lean theorem or whole-port binding yet.'},indent=2,sort_keys=True))
