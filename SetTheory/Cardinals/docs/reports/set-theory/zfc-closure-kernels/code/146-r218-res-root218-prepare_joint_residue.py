#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'k220_replay/baseline/K221_Construction_2026-10-20/portable'))
import source_language as s
raw=(ROOT/'baseline219/K219_Construction_2026-10-20/machine/sites219.json').read_bytes()
rows=json.loads(raw);g,c=s.graph_arithmetic(rows);assert g==s.graph_intervals(rows)
cert=json.loads((ROOT/'machine218/abstract219.json').read_text());assert cert['source_sha256']==hashlib.sha256(raw).hexdigest();dom=cert['domains']
with (ROOT/'root218/joint_residue.in').open('w') as f:
 f.write(str(len(rows))+'\n')
 for i,((_,op,r),(_,targets)) in enumerate(zip(rows,g)):
  k={'CI':0,'CD':1,'CB':2,'CC':3,'CH':4}[op]
  f.write(f'{k} {r or 0} {targets[0] if targets else -1} {targets[1] if len(targets)>1 else -1} {dom[i][r] if dom[i] and op in ("CI","CD") else 0}\n')
print('PREPARED',len(rows),'exact source CFG rows')
