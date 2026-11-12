#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;D=P.parents[1]
r=(D/'research/adaptive-aq20-substituted-scales104/candidate.json').read_bytes();assert hashlib.sha256(r).hexdigest()=='e21601ed2d0a17aa72ad1bbe103122337ecf98455cf39d9e97a22883d1c9ab50'
p=json.loads(r);removed={'M','root_btq3','firstScaledDelta','firstDeltaMinusY'};rows=[]
for r in p['source']:
 if r[0] in removed:continue
 if r[0]=='zDifference':
  rows.extend([['zInner','*','qm','firstDelta'],['zMerged','+','zInner','Bt'],['zScaled','*','q3','zMerged']]);r=['zDifference','-','zScaled','g33']
 rows.append(r)
c={'scope':'External candidate; Lean zero-map and iPRA endpoint are open.','parent_sha256':hashlib.sha256((D/'research/adaptive-aq20-substituted-scales104/candidate.json').read_bytes()).hexdigest(),'witnesses':p['witnesses'],'fixed_numerals':p['fixed_numerals'],'source':rows,'output':p['output'],'operations':len(rows)}
cr=(json.dumps(c,indent=2)+'\n').encode();(P/'candidate.json').write_bytes(cr)
ren={n:'n_'+n for n in c['witnesses']};rep=lambda x:'shift_'+x if isinstance(x,str) and x in ren else x
ns=[['shift_'+n,'+',ren[n],1] for n in c['witnesses']]+[[n,o,rep(a),rep(b)] for n,o,a,b in rows]
n={'scope':'Natural-variable shifted external candidate; Lean endpoint open.','positive_parent_sha256':hashlib.sha256(cr).hexdigest(),'witnesses':[ren[n] for n in c['witnesses']],'fixed_numerals':p['fixed_numerals'],'source':ns,'output':c['output'],'operations':len(ns)}
(P/'natural-candidate.json').write_text(json.dumps(n,indent=2)+'\n')
