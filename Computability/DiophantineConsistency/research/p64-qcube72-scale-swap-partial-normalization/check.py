#!/usr/bin/env python3
"""Exact controls for a symbolic scale/transport swap; no graph-zero claim."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
 raise SystemExit('requires python3 -I -S -B without optimization')
root=Path(__file__).resolve().parents[2]
pins={
 'research/p64-qcube72-free-main-candidate/P64QCube72FreeForward.lean':'7256e6dd921e74a3ecf013f60e4ab512b6313d728c9538665f8f629fcfbd408c',
 'research/p64-qcube72-fixed-compact-ranked-main-draft/FreeMainFixedCompactRankedMain.lean':'79eedcd56d95f2cc761609536bcf19c28119d2889806d0d3b480d573fa938159',
 'research/p64-qcube72-divisible-q-no-old-gamma-draft/FreeMainDivisibleQNoOldGamma.lean':'c986b3c588a74730991681805d906e611435915fb54fd81128a4e67779720564',
 'research/p64-qcube72-main-root-draft/FreeMainGraphMainRoot.lean':'97330ce58ce6f52ade485957cb97ed23e7d8638983457d067c20797faff2be76',
 'research/p64-qcube76y-fixed-q-not-three-draft/FreeMain76FixedQNotThree.lean':'2366738263d44e4f47151cdd0bddcdc6df5248f03f21f90b225d03494e647e0a'}
for f,h in pins.items():
 if hashlib.sha256((root/f).read_bytes()).hexdigest()!=h:raise RuntimeError('pin mismatch '+f)
if (pow(2,590069,3)-1)%3!=1:raise RuntimeError('fixed beta residue')
count=0;blocked=0
for beta in range(4,65,3):
 q=2*beta+1; qp=beta+1
 for u in range(1,6):
  for t in range(1,5):
   w=qp*u; s=qp**3*t; wp=u*q; sp=q**3*t
   if w*q!=wp*qp or q**3*s!=qp**3*sp:raise RuntimeError('scale mismatch')
   for K in range(0,2*beta+1):
    A=K+wp;r=A%beta
    if r==0:
     blocked+=1
     for C in range(1,beta):
      if (A*C)%beta:raise RuntimeError('blocked transport control')
     continue
    C=1; F=r; alpha=beta-r; z=A//beta
    if not (0<F and 0<alpha and 0<z and F+alpha+C==qp and A*C==F+z*(qp-1)):
     raise RuntimeError('transport normalization')
    count+=1
print(json.dumps({'status':'PASS_FINITE_CONTROLS','transport_controls':count,'blocked_residue_controls':blocked,'beta_range':[4,64,3],'u_range':[1,5],'t_range':[1,4],'fixed_beta_mod_3':1,'pins':pins,'scope':'Exact small-integer controls for symbolic scale and transport only; no graph zero or full normalization asserted.'},sort_keys=True))
