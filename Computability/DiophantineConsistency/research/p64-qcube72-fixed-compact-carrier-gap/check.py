#!/usr/bin/env python3
"""Finite controls for a standard-integer divisibility reduction."""
import hashlib,json,math,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
 raise SystemExit('requires python3 -I -S -B without optimization')
root=Path(__file__).resolve().parents[2]
pins={
 'Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean':'374719597b3126504fc7b4daeb8ce08a7bae36c911ed37d8fee3d90ed324a5d5',
 'Lean/DiophantineConsistency/Compact44/P64Early.lean':'4db7d2153b1849d4646503244f7a5f2df031ddbeda4f135194b836ea125a02c1',
 'Lean/DiophantineConsistency/Compact44/P72Mu.lean':'088444b0f0dd2339aa630d8b3712b7af699ccecc5a0a83a84fe89486ce9f1c91',
 'research/p64-qcube72-equal-rank-first-index-obstruction/check.py':'20146e38397f75bf678a91061a0f2687b9876123ba4a91cdc011104281ab2ac8',
 'research/p64-qcube72-fixed-compact-index-window-draft/FreeMainFixedCompactIndexWindow.lean':'5f4328358031cdabc3d32a0bb2c34c96c7da7d01b5c95babf7161b06f568674f',
}
for name,digest in pins.items():
 if hashlib.sha256((root/name).read_bytes()).hexdigest()!=digest:raise RuntimeError('pin mismatch '+name)
prior=subprocess.run([sys.executable,'-I','-S','-B',str(root/'research/p64-qcube72-equal-rank-first-index-obstruction/check.py')],capture_output=True,text=True,timeout=20,check=True)
a=json.loads(prior.stdout)
if (a['m'],a['j'],a['h_mod_729'],a['k_mod_729'],a['old_carrier_mod_729'],a['mu'])!=(19259,11720,486,112,292,243):raise RuntimeError('negative-control mismatch')
count=0;eligible=0;residues={}
for q in range(3,11):
 for s in range(1,5):
  Y=q**3*s; U=Y*Y
  for w in range(1,6):
   X=w*q; H=4*((X+1)*Y)+3; e=math.gcd(U,H); mu=U//e
   if 9%e or mu<q**4:raise RuntimeError('gcd/size premise')
   for R in range(5,31):
    for n in range(1,R):
     if R>=2*n:continue
     d=2*n-R-1
     if not 0<=d<R+1<q**4<=mu:raise RuntimeError('gap bound')
     for r in range(1,e+2):
      h=mu*r
      if U*(H//e*r)!=H*h:raise RuntimeError('carrier relation')
      for lam in (0,1):
       k=2*n+4*X*U*lam
       numerator=h+k-R-1
       if numerator<=0:raise RuntimeError('gamma positivity')
       has_gamma=(numerator%U==0)
       criterion=(d==0 and h%U==0)
       if has_gamma!=criterion:raise RuntimeError('criterion mismatch')
       count+=1
       if has_gamma:eligible+=1
       residues[str(e)]=residues.get(str(e),0)+1
print(json.dumps({'status':'PASS_FINITE_CONTROLS','control_cases':count,'cases_with_gamma':eligible,'gcd_case_counts':residues,'counterexample':{'R':19259,'n':11720,'gap':4180,'mu':243,'gap_mod_mu':4180%243,'h_mod_U':486,'old_carrier_mod_U':292,'compact_window':'fails'},'pins':pins,'scope':'Finite integer controls and source pins; general divisibility proof is in README and no IΣ₁-model theorem is asserted.'},sort_keys=True))
