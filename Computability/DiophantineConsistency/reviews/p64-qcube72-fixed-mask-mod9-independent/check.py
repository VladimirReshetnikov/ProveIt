#!/usr/bin/env python3
"""Independent exact fixed-mask reconstruction and mod-9 graph checks."""
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B without optimization')
root=Path(__file__).resolve().parents[2]
packet=root/'research/p64-qcube72-fixed-mask-mod9-controls'
graph=root/'research/p64-qcube72-free-main-candidate/graph.json'
compact=root/'Lean/DiophantineConsistency/Compact44'
pins={packet/'check.py':'eb92c1f0ca861e5aa1771a670e8aff4f31d46e97988f0275aa12349ad4c9c3ec',
 packet/'result.json':'16d921974a6c7fc1363813613bf30ef48f5e85ed4d829873809ba1709a7921fd',
 graph:'875a9d0972c350e6858e25b68f2dc794b1f330e61f29cd52a5853ece90b24806',
 compact/'CompactSymbolicPorts.lean':'0fc8eb4f60e801b38a3a516cd23d9f44c1e9eda62609d34bd76764de7ac51414',
 compact/'CompactFixedBeta.lean':'bcb892e7ae6b0d3cf329a248ca6b468e36a9a1b582d75cacafb7fd49f89025ea',
 compact/'CompactListMask.lean':'34c4d38c265160155a7fa3f99ea3af692c5f3be10b7b77cac211afc199953d4b',
 compact/'CompactConcreteMask.lean':'f93993e8b4badb6518d8ac6e575d406f322d7205b7d95c17c185103510b474c2',
 compact/'CompactHighPopulation.lean':'b1e962aed2f9fc2b49533a52f3508a84af4d433c4a9fae210540e085056dab1d'}
for p,h in pins.items():
    if hashlib.sha256(p.read_bytes()).hexdigest()!=h:raise RuntimeError('source mismatch '+str(p))

# Build the actual fixed numerals, independently of the author's modular
# digit sum. Nat.ofDigits is little-endian; the symbolic low recipe subtracts
# one power per support point and two further powers at the special point.
support=(set(range(943))|set(range(983,993))|set(range(1003,1012))|
         set(range(1013,1032))|{1063,1064,1095,2195,3296})-{1}
digits=([4]+[0]*1012+[1]*10+[0]*42+[1]*9+[0]*1121+[1]+[0]*1100+[1]+
        [0]*1096+[(1<<51)-2]+[0]*1101+[(1<<51)-2]+[0]*3296+
        [((1<<65)-1)]*13+[(1<<19)-1,0])
if len(support)!=985 or len(digits)!=8807:raise RuntimeError('digit transcription shape')
beta=(1<<(67*8807))-1
low=beta-sum(1<<(67*j) for j in support)-2*(1<<(67*1063))
high=sum(d<<(67*j) for j,d in enumerate(digits) if d)
residues=(beta%9,low%9,high%9,(beta+high)%9)
if residues!=(4,1,3,7):raise RuntimeError('fixed residue mismatch')

dag=json.loads(graph.read_bytes()); rows=dag['source']; results=[]; total=0
for J,K,alpha,s,q in ((2,8,7,1,0),(1,4,3,9,5)):
    for lowmod in range(9):
        for highmod in range(9):
            env={'beta':4,'K0':K,'MC':lowmod,'MF':highmod,'J':J,'F':1,'alpha':alpha,
                 'z':1,'f':1,'i':1,'T':1,'s':s,'w':1,'t':1,'eta':3,'zeta':1,'y':1,'h':1}
            for name,op,l,r in rows:
                l=env[l] if isinstance(l,str) else l; r=env[r] if isinstance(r,str) else r
                if op=='+': value=l+r
                elif op=='-': value=l-r
                elif op=='*': value=l*r
                else: raise RuntimeError('unknown graph operation')
                env[name]=value%9
            want={'q':q,'Y':0,'U':0,'H':3,'Delta':3,'A0':1,'Na':1,'M':0,'W':0,'Lt':0,'polynomial':0}
            if any(env[n]!=v for n,v in want.items()):raise RuntimeError('graph residual mismatch')
            if (lowmod,highmod)==(1,7):results.append({'J':J,'K':K,'alpha':alpha,'s':s,'q_mod9':q})
            total+=1
author=json.loads((packet/'result.json').read_text())
if len(rows)!=72 or total!=162 or author['arbitrary_mask_cases']!=total or len(results)!=2:
    raise RuntimeError('case count mismatch')
print(json.dumps({'status':'PASS','fixed_residues':residues,'actual_beta_bits':beta.bit_length(),
 'graph_rows':len(rows),'arbitrary_mask_cases':total,'fixed_cases':results,
 'scope':'Two modular graph zeros, not integer zeros or model existence claims.'},sort_keys=True))
