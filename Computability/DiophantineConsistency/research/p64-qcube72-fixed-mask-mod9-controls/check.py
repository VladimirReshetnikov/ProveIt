#!/usr/bin/env python3
"""Exact fixed-port residues and two complete 72-graph mod-9 controls."""
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
beta=(pow(2,590069,9)-1)%9;B=pow(2,67,9)
support=(set(range(943))|set(range(983,993))|set(range(1003,1012))|set(range(1013,1032))|{1063,1064,1095,2195,3296})-{1}
highdigits=([4]+[0]*1012+[1]*10+[0]*42+[1]*9+[0]*1121+[1]+[0]*1100+[1]+[0]*1096+[(1<<51)-2]+[0]*1101+[(1<<51)-2]+[0]*3296+[((1<<65)-1)]*13+[(1<<19)-1,0])
if len(support)!=985 or len(highdigits)!=8807:raise RuntimeError('digit transcription shape')
low=(beta-sum(pow(B,j,9) for j in support)-2*pow(B,1063,9))%9
high=sum(x*pow(B,j,9) for j,x in enumerate(highdigits))%9
MF=(beta+high)%9
if (beta,B,low,high,MF)!=(4,2,1,3,7):raise RuntimeError('fixed port residues')
a=json.loads((root/'research/p64-qcube72-free-main-candidate/graph.json').read_bytes())
ops={'+':operator.add,'-':operator.sub,'*':operator.mul}
cases=[]; total=0
for J,K,alpha,s,expected_q in ((2,8,7,1,0),(1,4,3,9,5)):
 summary=None
 for MC in range(9):
  for M in range(9):
   v={'beta':beta,'K0':K,'MC':MC,'MF':M,'J':J,'F':1,'alpha':alpha,'z':1,'f':1,'i':1,'T':1,'s':s,'w':1,'t':1,'eta':3,'zeta':1,'y':1,'h':1}
   d={k:x%9 for k,x in v.items()}
   for name,op,x,y in a['source']:
    d[name]=ops[op](d[x] if isinstance(x,str) else x,d[y] if isinstance(y,str) else y)%9
   target={'q':expected_q,'Y':0,'U':0,'H':3,'Delta':3,'A0':1,'M':0,'W':0,'Na':1,'Lt':0,'polynomial':0}
   if any(d[k]!=val for k,val in target.items()):raise RuntimeError('residual mismatch')
   if MC==low and M==MF:summary={k:d[k] for k in target}
   total+=1
 if summary is None:raise RuntimeError('actual fixed masks missing')
 cases.append({'J':J,'K':K,'alpha':alpha,'s':s,'residuals_at_fixed_masks':summary})
print(json.dumps({'status':'PASS_MODULAR_CONTROLS','fixed_port_residues_mod_9':{'beta':beta,'MC':low,'high':high,'MF':MF},'cases':cases,'arbitrary_mask_cases':total,'pins':pins,'scope':'Two complete graph evaluations modulo 9, with actual fixed port residues; no integer zero or existence claim.'},sort_keys=True))
