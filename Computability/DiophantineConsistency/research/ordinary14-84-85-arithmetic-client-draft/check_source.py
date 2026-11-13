#!/usr/bin/env python3
"""Source/interface inventory and dependency replays; never invokes Lean."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
D=Path(__file__).resolve().parents[2]; H=Path(__file__).resolve().parent
src=H/'ArithmeticComparison.lean'; s=src.read_text()
for name in ('from84_with_carrier','from85_with_mersenne'):
 assert re.search(r'\btheorem\s+'+name+r'\b',s)
for term in ('gamma_gt_from_modified_balance','mersenne_divides_X','map_84_to_85','map_85_to_84','(hR : 3≤R)','(hdiv : q beta v∣3*v 6)','(hbal :','(hz :'):
 assert term in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
for name in ('ordinary14-84-85-conditional-model-draft','ordinary14-modified-carrier-model-facts-draft','ordinary14-modified-carrier-gamma-model-draft'):
 p=D/'research'/name
 scripts=list(p.glob('check_source.py'))
 if not scripts: scripts=list(p.glob('check.py'))
 assert len(scripts)==1,(name,scripts)
 r=subprocess.run([sys.executable,'-I','-S','-B',str(scripts[0])],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
 assert not r.stderr and r.stdout==(p/'observation.json').read_bytes(),name
paths=[src,D/'research/ordinary14-84-85-conditional-model-draft/ConditionalComparison.lean',D/'research/ordinary14-modified-carrier-model-facts-draft/ModifiedCarrierFacts.lean',D/'research/ordinary14-modified-carrier-gamma-model-draft/CarrierGamma.lean']
print(json.dumps({'scope':'source/interface inventory and dependency replays only; no Lean invocation','sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
