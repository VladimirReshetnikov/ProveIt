#!/usr/bin/env python3
"""Generate kernel-checkable CM215 table facts from hash-pinned native tables."""
from pathlib import Path
import argparse
import hashlib
import json

PIN = 'b6c7087477e51c017003bd729e712c8969733223'
HASHES = {
 'k215.native.tm': '9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2',
 'marker215.native.tm': 'e5907f08e0752eada0e25bbf33680341e80e5fe94b52b409aea1ed039edda252',
}

def parse(path):
 data=path.read_bytes()
 if hashlib.sha256(data).hexdigest()!=HASHES[path.name]:
  raise ValueError('Pinned source hash mismatch: '+str(path))
 rows={}
 for l in data.decode().splitlines():
  if not l or l.startswith('#'): continue
  q,b,w,d,n=l.split(); q,b,w,n=map(int,(q,b,w,n))
  if (q,b) in rows or b not in (0,1) or w not in (0,1) or d not in ('L','R') or not 0<=q<303 or not 0<=n<303:
   raise ValueError('Malformed row')
  rows[q,b]=(w,d,n)
 if len(rows)!=430 or len({q for q,b in rows})!=215:
  raise ValueError('Wrong state census')
 if any((q,1-b) not in rows for q,b in rows):
  raise ValueError('Partial working state')
 return rows

def row(r):
 w,d,n=r
 return f'⟨{str(bool(w)).lower()}, {str(d=="R").lower()}, {n}⟩'

def array(name,rows):
 lines=[f'def {name}Table : Table := fun q b =>', '  match q.val with']
 for q in sorted({q for q,b in rows}):
  lines.append(f'  | {q} => some (if b then {row(rows[q,1])} else {row(rows[q,0])})')
 lines += ['  | _ => none', '']
 return '\n'.join(lines)

