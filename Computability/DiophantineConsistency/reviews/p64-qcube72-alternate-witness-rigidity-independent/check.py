#!/usr/bin/env python3
"""Independent source pins and bounded arithmetic controls; no Lean replay."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('run with python3 -I -S -B')
ROOT = Path(__file__).resolve().parents[2]
pins = {
 'research/p64-qcube72-alternate-witness-rigidity/README.md':'bcabc67c618ee6931c973e10f4ede4c8eb2aec4de1e355a6238b865c607f585e',
 'research/p64-qcube72-alternate-witness-rigidity/check.py':'400547fa93fa3206050731eb5e97fc7e5b888ad67dcb022c6eb955c16c3a7e4f',
 'Lean/DiophantineConsistency/Compact44/P64Facts.lean':'4edd062b84bf7b2bf131a7c3ff1a6125aa6fffc9e1ddb0ae9d5b13a60566f47a',
 'Lean/DiophantineConsistency/Compact44/P64Root.lean':'afcbb52982e7c1334e615029e4af554fbb53c86ee07e77070212d2edf47118f9',
 'Lean/DiophantineConsistency/Compact44/P72Power.lean':'f46584fb3977ae5fc33b31bee18e8c27435d97bea10138f163af2de5ee66d462',
 'research/p64-qcube76-independent-y-lemmas-draft/IndependentYWitnessDraft.lean':'b4f83f52f59bc0630b68cb5a301869e50e7805369ea86cd0b17d3a4fb906b51b',
 'research/fourteen-p64-qcube77-unit-draft/P64QCube77Existence.lean':'e65822241f4308d969094f91b68a90a5c267ad82b852b3b7b68f2fad769a942a',
 'research/fourteen-p64-qcube78-existence-draft/P64QCube78Existence.lean':'a5e64c5dfeed7752d80546d6ff3b61cff314767d64682c173f935734e22b3af7',
 'research/fourteen-p64-qcube79-gap-draft/P64QCube79Gap.lean':'8d7a3f88a31ca7b9895c21d6855260c7fec90880cd233671d8deb1533c7aed1f',
 'research/fourteen-p64-qcube80-existence-draft/P64QCube80Existence.lean':'f417cb3f09e4e9235e5e9cd85f083d14f8fd0e89b1b554dfbaaedc672cfdda10',
 'research/fourteen-p64-qcube-quotient-map-draft/P64QCubeMap.lean':'20bd2cc8803cea1b7b088b9150341045679076141f007c205aff2c1e92c49916',
}
for name, digest in pins.items():
    if hashlib.sha256((ROOT/name).read_bytes()).hexdigest() != digest:
        raise ValueError('source hash mismatch: '+name)

anchors = {
 'research/p64-qcube76-independent-y-lemmas-draft/IndependentYWitnessDraft.lean': ['Function.update v 12 e'],
 'research/fourteen-p64-qcube77-unit-draft/P64QCube77Existence.lean': ['theorem same_zero_iff'],
 'research/fourteen-p64-qcube78-existence-draft/P64QCube78Existence.lean': ['theorem same_zero_iff'],
 'research/fourteen-p64-qcube79-gap-draft/P64QCube79Gap.lean': ['Function.update v 9'],
 'research/fourteen-p64-qcube80-existence-draft/P64QCube80Existence.lean': ['Function.update v 9'],
 'research/fourteen-p64-qcube-quotient-map-draft/P64QCubeMap.lean': ['Function.update v 7'],
 'Lean/DiophantineConsistency/Compact44/P64Root.lean': ['theorem main_root', '(hb : 0 < (p 0 : V))', '(hY :'],
 'Lean/DiophantineConsistency/Compact44/P64Facts.lean': ['theorem facts_ports', 'P72Power.power_of_mod', 'have hX2 : X = Exp.exp R'],
 'Lean/DiophantineConsistency/Compact44/P72Power.lean': ['theorem power_of_mod', '(hnR : 2 * n = R + 1)', '(hmR : m = R)', '(hgmod :'],
}
for name, fragments in anchors.items():
    source=(ROOT/name).read_text()
    if any(fragment not in source for fragment in fragments):
        raise ValueError('missing source anchor: '+name)

# Independent enumeration permits negative h provided the evaluated root is
# positive. Equality of positive squares must then force equality of h.
cases=0
for X in range(1,9):
 for Y in range(1,9):
  U=Y*Y; H=4*(X+1)*Y+3
  for c in range(1,9):
   B=U*(X+(X+1)*Y*c)
   values=[(h,B+H*h) for h in range(-8,9) if B+H*h>0]
   for h1,d1 in values:
    for h2,d2 in values:
     if (d1*d1 == d2*d2) != (h1 == h2):
      raise ValueError('positive-root rigidity')
     cases+=1
# Positivity matters: the same square can arise from opposite roots.
assert 1+2*5+11*0 == 11 and 1+2*5+11*(-2) == -11

repunit_cases=0
for B in range(1,25):
 beta=(1<<B)-1
 for d in range(1,145):
  quotient,remainder=divmod((1<<d)-1,beta)
  if (remainder==0)!=(d%B==0): raise ValueError('repunit divisibility')
  if remainder==0:
   t=d//B
   if quotient != sum(1<<(B*j) for j in range(t)):
    raise ValueError('repunit quotient')
  repunit_cases+=1
assert pow(2,590069,3)==2

author=ROOT/'research/p64-qcube72-alternate-witness-rigidity/check.py'
got=subprocess.run([sys.executable,'-I','-S','-B',str(author)],capture_output=True,text=True,check=True)
expected=(ROOT/'research/p64-qcube72-alternate-witness-rigidity/result.json').read_text()
if got.stdout!=expected: raise ValueError('author controls do not reproduce')
print(json.dumps({'status':'PASS','pinned_sources':len(pins),
 'positive_root_cases':cases,'repunit_cases':repunit_cases,
 'negative_root_control':True,'author_controls':'reproduced',
 'scope':'standard integer source audit; no Lean replay, fixed-port zero or witness-conversion theorem'},sort_keys=True))
