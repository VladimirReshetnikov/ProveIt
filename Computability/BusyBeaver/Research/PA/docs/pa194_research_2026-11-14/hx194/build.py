#!/usr/bin/env python3
"""Deterministically reconstruct or check PA194HX from the pinned baseline.
Only the two logical-register router rows change. This is not an arithmetic
calibration proof. Run without -O; no dependencies beyond Python's stdlib.
"""
from pathlib import Path
import argparse,hashlib,json
ROOT=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('--write',action='store_true');a=p.parse_args()
assert __debug__
raw=(ROOT/'inputs/primary194.native.tm').read_bytes()
assert hashlib.sha256(raw).hexdigest()=='e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54'
old={}
for line in raw.decode().splitlines():
 q,b,w,d,t=line.split();old[int(q),int(b)]=int(w),d,int(t)
assert old[21,1]==(0,'R',60) and old[45,1]==(0,'R',55)
rows=dict(old);rows[21,1]=(0,'R',55);rows[45,1]=(0,'R',60)
states={q for q,b in rows};assert len(states)==194 and len(rows)==388
assert set(rows)=={(q,b)for q in states for b in (0,1)}
assert {t for w,d,t in rows.values()}-states=={254}
order=[74];labels={74:0}
for q in order:
 for b in (0,1):
  t=rows[q,b][2]
  if t!=254 and t not in labels:labels[t]=len(order);order.append(t)
assert len(order)==194
native=''.join(f'{q} {b} {w} {d} {t}\n'for(q,b),(w,d,t)in sorted(rows.items()))
dense=''.join(f'{i} {b} {rows[q,b][0]} {rows[q,b][1]} {194 if rows[q,b][2]==254 else labels[rows[q,b][2]]}\n'for i,q in enumerate(order)for b in (0,1))
files={'pa194hx.native.tm':native,'pa194hx.tm':dense,'pa194hx.labels.json':json.dumps(order+[254])}
for name,s in files.items():
 path=ROOT/'machine'/name
 if a.write:path.write_text(s)
 assert path.read_bytes()==s.encode(),name
print(json.dumps({'status':'PASS','working_states':194,'rows':388,'native_start':74,'native_halt':254,'dense_start':0,'dense_halt':194,'edits':[[21,1,0,'R',55],[45,1,0,'R',60]],'sha256':{n:hashlib.sha256(s.encode()).hexdigest()for n,s in files.items()}},indent=2))
