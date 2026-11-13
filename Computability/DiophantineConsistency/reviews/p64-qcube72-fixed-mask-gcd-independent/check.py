#!/usr/bin/env python3
"""Independent fixed-mask reconstruction, residue proof and small controls."""
import hashlib
import json
import operator
import subprocess
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B without optimization')
root=Path(__file__).resolve().parents[2]
packet=root/'research/p64-qcube72-fixed-mask-gcd-obstruction'
compact=root/'Lean/DiophantineConsistency/Compact44'
graph=root/'research/p64-qcube72-free-main-candidate/graph.json'
pins={packet/'check.py':'99d8251f6268e955ebe7af008e78c1fd5c0241ba6ae9ac7041b9877662a92fa3',
 packet/'result.json':'15c119c08c38b7d334d844aae656c4ec86dc68169a29673a8a5f9abc54bd74bf',
 graph:'875a9d0972c350e6858e25b68f2dc794b1f330e61f29cd52a5853ece90b24806',
 compact/'CompactSymbolicPorts.lean':'0fc8eb4f60e801b38a3a516cd23d9f44c1e9eda62609d34bd76764de7ac51414',
 compact/'CompactFixedBeta.lean':'bcb892e7ae6b0d3cf329a248ca6b468e36a9a1b582d75cacafb7fd49f89025ea',
 compact/'CompactListMask.lean':'34c4d38c265160155a7fa3f99ea3af692c5f3be10b7b77cac211afc199953d4b',
 compact/'CompactConcreteMask.lean':'f93993e8b4badb6518d8ac6e575d406f322d7205b7d95c17c185103510b474c2',
 compact/'CompactHighPopulation.lean':'b1e962aed2f9fc2b49533a52f3508a84af4d433c4a9fae210540e085056dab1d'}
for p,h in pins.items():
    if hashlib.sha256(p.read_bytes()).hexdigest()!=h:raise RuntimeError('source mismatch '+str(p))

# Explicit independent transcription of the pinned list definitions; Nat.ofDigits
# is little-endian. Compute actual masks but never print their large integers.
B=1<<67; length=8807; special=1063
support=(set(range(943))|set(range(983,993))|set(range(1003,1012))|
         set(range(1013,1032))|{1063,1064,1095,2195,3296})-{1}
if len(support)!=985 or not all(0<=j<length for j in support) or special not in support:
    raise RuntimeError('support transcription')
beta=(1<<(67*length))-1
low=beta-sum(1<<(67*j) for j in support)-2*(1<<(67*special))
highdigits=([4]+[0]*1012+[1]*10+[0]*42+[1]*9+[0]*1121+[1]+[0]*1100+[1]+
            [0]*1096+[(1<<51)-2]+[0]*1101+[(1<<51)-2]+[0]*3296+
            [((1<<65)-1)]*13+[(1<<19)-1,0])
if len(highdigits)!=length or not all(0<=x<B for x in highdigits):raise RuntimeError('high digit transcription')
high=sum(x<<(67*j) for j,x in enumerate(highdigits) if x)
if not (0<=low<beta and 0<high<beta and beta%9==4):raise RuntimeError('actual mask bounds or beta residue')

cases=[]
for J,s,w,e in ((1,1,1,1),(2,1,1,3),(1,3,3,9)):
    q=beta*J+1; MF=beta+high; C=q-1-(q-2)
    rank=(q*q-q-1)*(q*q-1)+(low+q*MF)*J
    if not (q>w and C==1 and (q-w+w)*C==1+(q-1) and rank+1<q**4):
        raise RuntimeError('actual fixed-mask transport/rank bounds')
    qm=q%9; ym=(qm**3*s)%9; hm=(4*(w*qm+1)*ym+3)%9
    if (qm,ym,hm)!=({1:(5,8,6),3:(0,0,3),9:(5,6,0)}[e]):
        raise RuntimeError('modular gcd certificate')
    cases.append({'e':e,'q_mod9':qm,'Y_mod9':ym,'H_mod9':hm})

# Independently reproduce the author's complete finite control output.
run=subprocess.run([sys.executable,'-I','-S','-B',str(packet/'check.py')],
                   check=True,capture_output=True,text=True,timeout=30)
if json.loads(run.stdout)!=json.loads((packet/'result.json').read_text()):raise RuntimeError('author control result mismatch')
print(json.dumps({'status':'PASS','actual_beta_bits':beta.bit_length(),'actual_low_bits':low.bit_length(),
 'actual_high_bits':high.bit_length(),'fixed_rank_cases':cases,'author_finite_controls':132,
 'scope':'Exact fixed-port masks/rank and symbolic partial assignments; no full zero or Lean proof'},sort_keys=True))
