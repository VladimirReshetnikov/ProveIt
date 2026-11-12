#!/usr/bin/env python3
"""Source inventory and finite ring/natural controls; never invokes Lean."""
from pathlib import Path
import hashlib,json,math,re,subprocess,sys
D=Path(__file__).resolve().parents[2];H=Path(__file__).resolve().parent
paths=[H/'RingNormExtraction.lean',D/'research/ordinary14-aux-norms-to-bounds-draft/NormsToBounds.lean',D/'Lean/DiophantineConsistency/ArithmeticAdaptiveQuotients2011.lean',D/'Lean/DiophantineConsistency/ModelDifferenceRing.lean']
s=paths[0].read_text()
for name in ('root_of_scaled_ring_square','first_norm_of_ring_residual','strong_norm_of_ring_residual','bounds_of_direct_field_residuals'):
 assert re.search(r'\btheorem\s+'+name+r'\b',s)
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
assert 'nonneg_or_nonpos Z' in s and '(hU : 0<U)' in s and '(hDeltaDef :' in s
scaled=first=strong=0;signs=set()
for U in range(1,10):
 for n in range(100):
  for z in range(-100,101):
   if z*z==U*U*n:
    d=math.isqrt(n);assert d*d==n;scaled+=1;signs.add((z>0)-(z<0))
assert signs=={-1,0,1}
for X in range(1,7):
 for Y in range(1,7):
  for eta in range(1,5):
   for zeta in range(1,5):
    k=eta+zeta;ell=X*Y*Y*k;first+=1
    assert 1+ell*(ell+k)==1+(X*Y*Y)*(X*Y*Y+1)*k*k
    a=X*Y+Y;delta=3+4*a+a*a;assert (a+2)**2==delta+1
for c in range(1,7):
 for i in range(1,5):
  for delta in range(1,15):
   for f in range(0,9):
    I=i*c*c
    assert (I*I-delta*(f*f-1)==0)==(I*I+delta==delta*f*f);strong+=1
p=D/'research/ordinary14-aux-norms-to-bounds-draft';r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60);assert not r.stderr and r.stdout==(p/'observation.json').read_bytes()
print(json.dumps({'scope':'source inventory, finite signed/natural controls and component receipt replay only; no Lean invocation','scaled_cases':scaled,'first_cases':first,'strong_cases':strong,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
