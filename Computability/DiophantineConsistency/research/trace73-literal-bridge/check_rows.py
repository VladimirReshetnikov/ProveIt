#!/usr/bin/env python3
"""Independently parse the literal Lean rows and compare to the candidate DAG."""
from pathlib import Path
from hashlib import sha256
import json,re,sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize: raise SystemExit('use python3 -I -S -B')
h=Path(__file__).resolve().parent; c=h.parent/'trace73-center-probe/candidate.json'; l=h/'Trace73Literal.lean'
sha=lambda p: sha256(p.read_bytes()).hexdigest()
pins={c:'c83151606214c211993fa0c5b9913abae3b6bcf2b00af107e599e4855f936ca6',l:'4413d7cce772dcb3d3c48881ea43ec891d5ecbebeab030228ef7aebcd95fd283'}
for p,d in pins.items():
 if sha(p)!=d: raise SystemExit('pin mismatch')
g=json.loads(c.read_bytes()); text=l.read_text(); rows=re.findall(r'^  let (g\d\d) := (\(v \d+\)|\(p \d+\)|g\d\d|\d+) ([+*\-]) (\(v \d+\)|\(p \d+\)|g\d\d|\d+)$',text,re.M)
if len(rows)!=73 or len(g['source'])!=73: raise SystemExit('wrong row count')
seen={f'(v {i})':name for i,name in enumerate(g['witnesses'])}; seen.update({f'(p {i})':name for i,name in enumerate(g['fixed_numerals'])})
for i,((node,op,a,b),(actual,x,oper,y)) in enumerate(zip(g['source'],rows),1):
 def decode(z): return int(z) if z.isdecimal() else seen[z]
 if actual!=f'g{i:02}' or [oper,decode(x),decode(y)]!=[op,a,b]: raise SystemExit(f'row {i} mismatch')
 seen[actual]=node
if not re.search(r'^  g73$',text,re.M) or seen['g73']!=g['output']: raise SystemExit('output mismatch')
for p,d in pins.items():
 if sha(p)!=d: raise SystemExit('final pin mismatch')
print(json.dumps({'status':'PASS','rows':len(rows),'candidate_sha256':sha(c),'lean_sha256':sha(l),'scope':'external parse of candidate and literal Lean source; JSON parsing is not formalized'},sort_keys=True,indent=2))
