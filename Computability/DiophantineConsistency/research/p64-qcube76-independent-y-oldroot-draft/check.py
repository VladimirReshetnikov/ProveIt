#!/usr/bin/env python3
"""Finite sanity checks for the old-root nonzero argument, not a Lean proof."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
p=Path(__file__).resolve(); old=0; lower=0
for A in range(2,101):
    for v in range(-100,101):
        if A*v*v==1: raise RuntimeError('unexpected discrete unit')
        old+=1
if not (1*1*1==1 and 1*(-1)*(-1)==1): raise RuntimeError('boundary control failed')
for i in range(1,41):
    for c in range(3,81):
        A=(i*c*c)**2
        if A<2: raise RuntimeError('strong norm lower bound failed')
        lower+=1
result={'status':'PASS_FINITE_ONLY','script_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),
        'nonzero_cases':old,'strong_lower_cases':lower,'boundary_control':'A=1, v=±1',
        'scope':'Bounded integer sanity checks; no quantified model theorem, graph zero or Lean proof.'}
out=p.with_name('result.json'); payload=json.dumps(result,indent=2,sort_keys=True)+'\n'
if sys.argv[1:]==['--write']:
    with out.open('x') as f:f.write(payload)
elif sys.argv[1:]: raise SystemExit('usage: python3 -I -S -B check.py [--write]')
elif out.read_text()!=payload: raise SystemExit('result differs')
print(json.dumps(result,sort_keys=True))
