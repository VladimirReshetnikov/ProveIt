#!/usr/bin/env python3
"""Reparameterize Y = q^3*(n_Y+1) and cancel q^6 in the first norm."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;D=P.parents[1]
b=(D/'research/ordinary13-natural-cfold-forced-x95-degree28/candidate.json').read_bytes()
assert hashlib.sha256(b).hexdigest()=='5fd11fa456867a2ed4f3b5bc58db59caab0f58736019ee864403d62124aced4e'
p=json.loads(b);removed={'Y','M','g32','g33','g34','folded_q3Bt','Z','g38','g39','g42','A0'};rows=[]
for r in p['source']:
 if r[0] in removed:continue
 rows.append(r)
 if r[0]=='q3':rows.extend([['Yquot','+','n_Y',1],['Y','*','q3','Yquot']])
 if r[0]=='g41':rows.extend([['new_sum','+','folded_g31','Yquot'],['new_scaled','*','qm','new_sum'],['new_diff','-','new_scaled','Bt'],['new_sq','*','new_diff','new_diff'],['new_qm2','*','qm','qm'],['new_norm','*','new_qm2','g41'],['A0','-','new_sq','new_norm']])
c={'scope':'External candidate; Lean zero-map and iPRA endpoint are open.','positive_qcube_parent_sha256':hashlib.sha256(b).hexdigest(),'domain':'nonnegative integers','witnesses':p['witnesses'],'fixed_numerals':p['fixed_numerals'],'source':rows,'output':p['output'],'operations':len(rows)}
(P/'candidate.json').write_text(json.dumps(c,indent=2)+'\n')
