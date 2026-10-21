#!/usr/bin/env python3
"""Reconstruct Z215 exactly from the included pinned K215; no solver needed."""
from pathlib import Path
import argparse, hashlib, json
ROOT=Path(__file__).resolve().parent
PARENT='9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2'
SOURCE='17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba'
NATIVE='423c755b04ed0cd5be199178686657bf721540b858d0fb8f491239622d6d99fa'
DENSE='d7a9d557cd08ddb0ebb1960b7fed4892db64bd38af5e0c4ae3bff9a594838825'
def sha(raw):return hashlib.sha256(raw).hexdigest()
def reconstruct(out):
 raw=(ROOT/'baseline/k215.native.tm').read_bytes();source=(ROOT/'baseline/sites215.json').read_bytes()
 assert sha(raw)==PARENT and sha(source)==SOURCE
 assert raw.splitlines()[0]==b'#! start 0'
 table={}
 for line in raw.decode().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();key=int(q),int(b)
  assert key not in table and d in ('L','R')
  table[key]=int(w),d,int(z)
 assert table[198,0]==(1,'L',40)
 before=dict(table);table[198,0]=(0,'L',40)
 assert [k for k in table if table[k]!=before[k]]==[(198,0)]
 states=sorted({q for q,b in table});assert len(states)==215 and len(table)==430
 assert set(table)=={(q,b) for q in states for b in (0,1)}
 reached,pending={74},[74]
 for q in pending:
  for b in (0,1):
   z=table[q,b][2];assert z==254 or z in states
   if z!=254 and z not in reached:reached.add(z);pending.append(z)
 assert reached==set(states)
 assert sum(w for w,d,z in before.values())==189
 assert sum(w for w,d,z in table.values())==188
 native=('#! start 74\n'+''.join(f'{q} {b} {w} {d} {z}\n' for (q,b),(w,d,z) in sorted(table.items()))).encode()
 order=[74]+[q for q in states if q!=74];mapping={q:i for i,q in enumerate(order)};mapping[254]=215
 dense=('#! start 0\n'+''.join(f'{mapping[q]} {b} {w} {d} {mapping[z]}\n' for q in order for b in (0,1) for w,d,z in [table[q,b]])).encode()
 assert sha(native)==NATIVE and sha(dense)==DENSE
 canonical=dict(native_start=74,dense_start=0,native_dispatcher=84,dense_dispatcher=mapping[84],native_halt=254,dense_halt=215,native_to_dense=mapping,dense_to_native={v:k for k,v in mapping.items()},native_sha256=sha(native),dense_sha256=sha(dense))
 out.mkdir(parents=True,exist_ok=False)
 (out/'z215.native.tm').write_bytes(native);(out/'z215.tm').write_bytes(dense);(out/'sites215.json').write_bytes(source)
 (out/'canonicalization.json').write_text(json.dumps(canonical,indent=2)+'\n')
 return dict(status='PASS',working_states=215,rows=430,graph_reachable_states=215,native_sha256=NATIVE,dense_sha256=DENSE,source_sha256=SOURCE,exact_changes=['initial state 0 -> 74','198/0: 1L40 -> 0L40'])
if __name__=='__main__':
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
 print(json.dumps(reconstruct(a.out),indent=2))
