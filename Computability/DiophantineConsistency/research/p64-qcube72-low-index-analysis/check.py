#!/usr/bin/env python3
"""Finite controls for the low-index algebra; no Lean."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B without optimization')
r=Path(__file__).resolve().parents[2];pins={r/'Lean/DiophantineConsistency/Compact44/P72Exact.lean':'a07730d92aefd39d86083d037f4772bacd7741788e2fff1f7669d33fa0ad05d3',r/'Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean':'63ec2a49f8d7066dbd8647a663db4bbd7255abd3ca7c3cc0d4d7b3533a189b16'}
for p,h in pins.items():
 if hashlib.sha256(p.read_bytes()).hexdigest()!=h:raise RuntimeError('source drift '+str(p))
cases=0;below=0;above=0
for q in range(5,21):
 for s in range(1,4):
  Y=q**3*s
  for w in range(1,61):
   X=q*w;P=X*Y*Y;a=(X+1)*Y;k=8*P+4;c=4*(a+2)**2-1;eta=c-k*Y
   A=(X-2*Y)*X+2*X+1
   if eta!=4*Y*Y*A+Y*(16*X+12)+15:raise RuntimeError('expanded eta mismatch')
   if X>=2*Y:
    if not eta>k:raise RuntimeError('upper branch failed')
    above+=1
   else:
    if not X<=2*Y-q or not eta<0:raise RuntimeError('lower branch failed')
    below+=1
   cases+=1
print(json.dumps({'status':'PASS_FINITE_CONTROLS','cases':cases,'below_branch':below,'above_branch':above,'scope':'Finite identities and inequalities only; the accompanying general argument is external mathematics, not a Lean theorem.'},sort_keys=True))
