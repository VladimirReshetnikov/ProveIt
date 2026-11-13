#!/usr/bin/env python3
"""Derive the two-quotient graph by explicit local rewrites; do not run Lean."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent; D=P.parents[1]
raw=(D/'research/adaptive-square-sums26-degree8/candidate.json').read_bytes()
assert hashlib.sha256(raw).hexdigest()=='d8e80e15d74271ba62877e841198a85729c0c4a74a5927927591b9ec2204b1a5'
p=json.loads(raw)
removed={'g39','g42','g62','g65','root_scaled','root_sum','ZComputed','g58','DstarComputed'}
replace={'g38':['g38','*','firstQuotient','firstQuotient'], 'A0':['A0','-','g38','g41'], 'g61':['g61','*','mainQuotient','mainQuotient'], 'A1':['A1','-','g61','g64'], 'zDifference':['zDifference','+','firstDeltaMinusY','root_btq3'], 'dDifference':['dDifference','-','mainScaledDelta','g59']}
rows=[]
for r in p['source']:
 if r[0] in removed:continue
 if r[0]=='zDifference':rows += [['firstDelta','-','firstQuotient','root_inner'],['firstScaledDelta','*','scaleVariable','firstDelta'],['firstDeltaMinusY','-','firstScaledDelta','g33']]
 if r[0]=='dDifference':rows += [['mainDelta','-','mainQuotient','b0'],['mainScaledDelta','*','mainScaleVariable','mainDelta']]
 rows.append(replace.get(r[0],r))
w=[{'zValueVariable':'firstQuotient','dValueVariable':'mainQuotient'}.get(n,n) for n in p['witnesses']]
c={'scope':'External candidate; Lean zero-map and iPRA endpoint are open.', 'parent_sha256':hashlib.sha256(raw).hexdigest(),'witnesses':w,'fixed_numerals':p['fixed_numerals'],'source':rows,'output':p['output'],'operations':len(rows)}
cr=(json.dumps(c,indent=2)+'\n').encode();(P/'candidate.json').write_bytes(cr)
ren={n:'n_'+n for n in w};rep=lambda x:'shift_'+x if isinstance(x,str) and x in ren else x
ns=[['shift_'+n,'+',ren[n],1] for n in w]+[[n,o,rep(a),rep(b)] for n,o,a,b in rows]
n={'scope':'Natural-variable shifted external candidate; Lean endpoint open.','positive_parent_sha256':hashlib.sha256(cr).hexdigest(),'witnesses':[ren[n] for n in w],'fixed_numerals':p['fixed_numerals'],'source':ns,'output':p['output'],'operations':len(ns)}
(P/'natural-candidate.json').write_text(json.dumps(n,indent=2)+'\n')
