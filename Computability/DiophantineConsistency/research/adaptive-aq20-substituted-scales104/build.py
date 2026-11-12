#!/usr/bin/env python3
"""Remove both scale coordinates by their existing binding expressions."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;D=P.parents[1]
r=(D/'research/adaptive-aq22-two-quotients110/candidate.json').read_bytes()
assert hashlib.sha256(r).hexdigest()=='b82ef3f8e45cc260d8ffee26f3f8fa7ef2f207834829aee1a5ac357fcab0ffc1'
p=json.loads(r);remove={'scaleDifference','scaleConstraint','finalWithScale','mainScaleDifference','mainScaleConstraint','finalWithMainScale'}
sub={'scaleVariable':'M','mainScaleVariable':'U','finalWithMainScale':'sumSquares'}
rows=[[n,o,sub.get(a,a),sub.get(b,b)] for n,o,a,b in p['source'] if n not in remove]
w=[n for n in p['witnesses'] if n not in ('scaleVariable','mainScaleVariable')]
c={'scope':'External candidate; Lean zero-map and iPRA endpoint are open.','parent_sha256':hashlib.sha256(r).hexdigest(),'witnesses':w,'fixed_numerals':p['fixed_numerals'],'source':rows,'output':p['output'],'operations':len(rows)}
cr=(json.dumps(c,indent=2)+'\n').encode();(P/'candidate.json').write_bytes(cr)
ren={n:'n_'+n for n in w};rep=lambda x:'shift_'+x if isinstance(x,str) and x in ren else x
ns=[['shift_'+n,'+',ren[n],1] for n in w]+[[n,o,rep(a),rep(b)] for n,o,a,b in rows]
n={'scope':'Natural-variable shifted external candidate; Lean endpoint open.','positive_parent_sha256':hashlib.sha256(cr).hexdigest(),'witnesses':[ren[n] for n in w],'fixed_numerals':p['fixed_numerals'],'source':ns,'output':p['output'],'operations':len(ns)}
(P/'natural-candidate.json').write_text(json.dumps(n,indent=2)+'\n')
