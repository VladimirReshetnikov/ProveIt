#!/usr/bin/env python3
"""Finite controls for the conditional free-carrier main-index lower bound."""
import hashlib,json,math,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B without optimization')
r=Path(__file__).resolve().parents[2];pins={r/'Lean/DiophantineConsistency/Compact44/P64Early.lean':'4db7d2153b1849d4646503244f7a5f2df031ddbeda4f135194b836ea125a02c1',r/'Lean/DiophantineConsistency/Compact44/P72Mu.lean':'088444b0f0dd2339aa630d8b3712b7af699ccecc5a0a83a84fe89486ce9f1c91',r/'Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean':'636b64ce7d7625603b41412ec6acade846e82e64bef36e55cd09cc0f1e09e390'}
for p,h in pins.items():
 if hashlib.sha256(p.read_bytes()).hexdigest()!=h:raise RuntimeError('source drift '+str(p))
cases=0;gcds=set()
for q in range(33,101):
 for s in range(1,4):
  Y=q**3*s;U=Y*Y
  for w in range(1,21):
   X=q*w;a=(X+1)*Y;H=4*a+3;e=math.gcd(U,H);mu=H//e
   if 9%e or H!=e*mu or not X<mu:raise RuntimeError('gcd/size bound')
   for m in range(6):
    if not 2**m<X or (U*(2**m-X))%H==0:raise RuntimeError('small index carrier congruence')
   gcds.add(e);cases+=1
print(json.dumps({'status':'PASS_FINITE_CONTROLS','parameter_cases':cases,'index_cases':cases*6,'observed_gcds':sorted(gcds),'scope':'Finite arithmetic controls; model-level conclusion requires the accompanying universal proof and a separate Lean check.'},sort_keys=True))
