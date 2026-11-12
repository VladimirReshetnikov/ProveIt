#!/usr/bin/env python3
"""Inventory and replay fact-level source checks; never invokes Lean."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
D=Path(__file__).resolve().parents[2];H=Path(__file__).resolve().parent
paths=[H/'NormsToBounds.lean',D/'research/ordinary14-model-main-square-gap-draft/MainSquareGap.lean',D/'research/ordinary14-aux-root-bounds-model-draft/AuxRootBounds.lean',D/'research/ordinary14-aux-geometry-model-draft/AuxGeometry.lean']
s=paths[0].read_text();assert re.search(r'\btheorem\s+aux_bounds_of_natural_norms\b',s)
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
for premise in ('(hX : 0<X)','(hY : 0<Y)','(heta : 0<eta)','(hzeta : 0<zeta)','(hi : 0<i)','(hcdef :','(hDelta :','(hfirst :','(hmain :','(hstrong :','(hQ :','(hz :'):
 assert premise in s
for n in ('ordinary14-model-main-square-gap-draft','ordinary14-aux-root-bounds-model-draft','ordinary14-aux-geometry-model-draft'):
 p=D/'research'/n
 r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=60)
 assert not r.stderr and r.stdout==(p/'observation.json').read_bytes()
print(json.dumps({'scope':'source inventory and component receipt replay only; no Lean invocation','components_replayed':3,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
