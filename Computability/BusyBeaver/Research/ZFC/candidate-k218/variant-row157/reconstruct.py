#!/usr/bin/env python3
"""Reconstruct the one-row K218 alternate; checking equivalence is separate."""
from pathlib import Path
import argparse,hashlib,json
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--source',type=Path,default=Path(__file__).resolve().parents[1]/'k218.native.tm')
p.add_argument('--output',type=Path,required=True)
a=p.parse_args();raw=a.source.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='2dfaba6da09b78291e534777cd30c5f0d68bd84faa670e868e779c396aeb308f'
assert not a.output.exists();a.output.mkdir(parents=True)
t={}
for line in raw.decode().splitlines():
 if not line or line.startswith('#'):continue
 q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z));assert(q,b)not in t;t[q,b]=(w,d,z)
assert len(t)==436 and t[157,1]==(1,'L',148)
t[157,1]=(1,'L',187)
def encode(T):return ('#! start 0\n'+''.join(f'{q} {b} {w} {d} {z}\n'for(q,b),(w,d,z)in sorted(T.items()))).encode()
native=encode(t);assert hashlib.sha256(native).hexdigest()=='3376bd149d5f35c03b3dabc79f095d2d2e674cf2e0e1c09a7de09431d8e74153'
(a.output/'k218-row157.native.tm').write_bytes(native)
mp={0:0};todo=[0]
for q in todo:
 for b in(0,1):
  z=t[q,b][2]
  if z!=254 and z not in mp:mp[z]=len(mp);todo.append(z)
assert set(mp)=={q for q,b in t}and len(mp)==218;mp[254]=218
can={(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in t.items()}
(a.output/'k218-row157.tm').write_bytes(encode(can))
(a.output/'map.json').write_text(json.dumps(mp,indent=2)+'\n')
print('EXACT_ONE_ROW_RECONSTRUCTION_PASS')
