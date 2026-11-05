#!/usr/bin/env python3
"""Bounded controls for uniform positive modular assignments at fixed masks."""
import hashlib,json,operator,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
 raise SystemExit('requires python3 -I -S -B without optimization')
root=Path(__file__).resolve().parents[2]
pins={
 'research/p64-qcube72-free-main-candidate/graph.json':'875a9d0972c350e6858e25b68f2dc794b1f330e61f29cd52a5853ece90b24806',
 'Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean':'0fc8eb4f60e801b38a3a516cd23d9f44c1e9eda62609d34bd76764de7ac51414',
 'Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean':'bcb892e7ae6b0d3cf329a248ca6b468e36a9a1b582d75cacafb7fd49f89025ea',
 'Lean/DiophantineConsistency/Compact44/CompactListMask.lean':'34c4d38c265160155a7fa3f99ea3af692c5f3be10b7b77cac211afc199953d4b',
 'Lean/DiophantineConsistency/Compact44/CompactConcreteMask.lean':'f93993e8b4badb6518d8ac6e575d406f322d7205b7d95c17c185103510b474c2',
 'Lean/DiophantineConsistency/Compact44/CompactHighPopulation.lean':'b1e962aed2f9fc2b49533a52f3508a84af4d433c4a9fae210540e085056dab1d'}
for f,h in pins.items():
 if hashlib.sha256((root/f).read_bytes()).hexdigest()!=h:raise RuntimeError('pin mismatch '+f)
support=(set(range(943))|set(range(983,993))|set(range(1003,1012))|set(range(1013,1032))|{1063,1064,1095,2195,3296})-{1}
highdigits=([4]+[0]*1012+[1]*10+[0]*42+[1]*9+[0]*1121+[1]+[0]*1100+[1]+[0]*1096+[(1<<51)-2]+[0]*1101+[(1<<51)-2]+[0]*3296+[((1<<65)-1)]*13+[(1<<19)-1,0])
if len(support)!=985 or len(highdigits)!=8807:raise RuntimeError('digit transcription shape')
a=json.loads((root/'research/p64-qcube72-free-main-candidate/graph.json').read_bytes());ops={'+':operator.add,'-':operator.sub,'*':operator.mul}
if (pow(2,590069,3)-1)%3!=1:raise RuntimeError('fixed beta mod 3')
count=0
for N in range(2,65):
 M=N**4; base=pow(2,67,M); beta=(pow(2,590069,M)-1)%M
 low=(beta-sum(pow(base,j,M) for j in support)-2*pow(base,1063,M))%M
 high=sum(x*pow(base,j,M) for j,x in enumerate(highdigits))%M
 for J in (1,2):
  q=(beta*J+1)%M
  v={'beta':beta,'K0':(q-1)%M,'MC':low,'MF':(beta+high)%M,'J':J,'F':1,'alpha':(q-2)%M,'z':1,'f':1,'i':1,'T':1,'s':N,'w':1,'t':1,'eta':N,'zeta':1,'y':1,'h':N}
  d={k:x%M for k,x in v.items()}
  for name,op,x,y in a['source']:d[name]=ops[op](d[x] if isinstance(x,str) else x,d[y] if isinstance(y,str) else y)%M
  if ((d['A0']-1)%(N*N) or d['M']%(N*N) or d['W']%M or d['Na']!=1%M or d['Lt'] or d['polynomial']):
   raise RuntimeError('modular residual mismatch')
  count+=1
print(json.dumps({'status':'PASS_BOUNDED_MODULAR_CONTROLS','moduli_tested':[2,64],'port_classes':2,'actual_fixed_mask_evaluations':count,'output_divisible_by':'N^4','pins':pins,'scope':'Finite graph residue controls support a separate all-positive-moduli symbolic proof; no integer zero or compatible p-adic limit asserted.'},sort_keys=True))
