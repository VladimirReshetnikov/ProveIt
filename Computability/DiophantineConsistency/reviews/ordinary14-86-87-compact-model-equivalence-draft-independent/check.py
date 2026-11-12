#!/usr/bin/env python3
"""Independent model-equivalence source wrapper review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-86-87-compact-model-equivalence-draft'
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,str(p);return b
pin(A/'README.md','2687b87320173706a202a1d952aa93d8de3c018903d2120f81b553f41e36a321')
s=pin(A/'CompactEquivalence8687.lean','3ba1bb233e7383358ea9bcd4f418eaf13aca1500fc45cc1cb2f981fb4df3c4ff').decode()
pin(A/'check_source.py','590c4b7b9339eb15b3ec6ab0b22ab3dee520cc4aea304023b20bf04a09c9808d')
receipt=pin(A/'observation.json','da46a5e68ebfd46c2813f294e6300c359598ea7281604b5ec403e789e21b7872')
for f in ['theorem positive_zero_iff (K : ℕ)', 'ports CompactFixedBeta.betaNat K lowNat highNat', 'let t : V := (67:V)*8807', 'C44Short15Facts.port_bounds', 'P72Root.cast_port p 0', 'P72Root.cast_port p 1', 'P72Root.cast_port p 2', 'P72Root.cast_port p 3', 'hp0 hp1 hp2 hp3 hb.2.1 hb.2.2.1', 't hb.1 hb.2.2.2 ht hradix']:assert f in s,f
for p,h in {'ordinary14-86-87-model-equivalence-draft/ModelEquivalence8687.lean': '7de67e77425498220b65e67991d7ec8b19cceb414ce5913c3df8d03c71350eea'}.items():pin(D/'research'/p,h)
r=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not r.stderr and r.stdout==receipt
print(json.dumps({'scope':'source wrapper and author-receipt review; no Lean','pinned_component_sources':1},sort_keys=True,indent=2))
