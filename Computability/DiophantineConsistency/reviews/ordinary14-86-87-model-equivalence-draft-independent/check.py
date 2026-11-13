#!/usr/bin/env python3
"""Independent model-equivalence source wrapper review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-86-87-model-equivalence-draft'
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,str(p);return b
pin(A/'README.md','38f66bacca89d82f8982556a28f5caf75f0cbf24fbcf0dc46a3aa416f3fee13c')
s=pin(A/'ModelEquivalence8687.lean','7de67e77425498220b65e67991d7ec8b19cceb414ce5913c3df8d03c71350eea').decode()
pin(A/'check_source.py','e4ea40692cebc713451fb1e26e5be6d4bf76daa5c7837cfce7409446eaf715da')
receipt=pin(A/'observation.json','4969645679d48d95e80cf28f0b0bbcfc48d7bd0eb996524c9a2b1b7e4fc9b6a7')
for f in ['(hbeta : 0<beta) (hbeta46 : 46≤beta) (ht : 4≤t) (hradix : beta=Exp.exp t-1)', 'P86ResidueGraph.graph p', 'P87ShiftedGuard.graph p', 'PositiveMap86To87Draft.positive_map p beta K v hport hK hv hz', 'ModelMap87To86Draft.positive_map p beta K MC MF t v hbeta hbeta46 ht hradix']:assert f in s,f
for p,h in {'ordinary14-86-to-87-positive-map-draft/PositiveMap86To87.lean': '439e4e88a6fa490c63e213c9434620d8e4459a2573b3b4d94993d9d369b510d5', 'ordinary14-87-to-86-model-map-draft/ModelMap87To86.lean': '3f602fc37d8e6be21d02dff60abd70948cc3f8b20266c7428e87d069d5d0546f'}.items():pin(D/'research'/p,h)
r=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not r.stderr and r.stdout==receipt
print(json.dumps({'scope':'source wrapper and author-receipt review; no Lean','pinned_component_sources':2},sort_keys=True,indent=2))
