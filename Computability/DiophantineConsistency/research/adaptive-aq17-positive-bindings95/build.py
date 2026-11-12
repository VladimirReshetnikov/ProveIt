#!/usr/bin/env python3
"""Remove three positive coordinates by their existing binding expressions."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;D=P.parents[1]
r=(D/'research/adaptive-aq20-substituted-scales104/candidate.json').read_bytes()
assert hashlib.sha256(r).hexdigest()=='e21601ed2d0a17aa72ad1bbe103122337ecf98455cf39d9e97a22883d1c9ab50'
p=json.loads(r);remove={'ellDifference','ellConstraint','addEll','cSquareDifference','cSquareConstraint','addCSquare','deltaDifference','deltaConstraint','addDELTAConstraint'}
sub={'ellVariable':'ell','cSquareVariable':'c2','deltaVariable':'DeltaComputed','addCSquare':'finalWithRank'}
rows=[[n,o,sub.get(a,a),sub.get(b,b)] for n,o,a,b in p['source'] if n not in remove]
w=[n for n in p['witnesses'] if n not in ('ellVariable','cSquareVariable','deltaVariable')]
c={'scope':'External candidate; Lean zero-map and iPRA endpoint are open.','parent_sha256':hashlib.sha256(r).hexdigest(),'witnesses':w,'fixed_numerals':p['fixed_numerals'],'source':rows,'output':'addVConstraint','operations':len(rows)}
cr=(json.dumps(c,indent=2)+'\n').encode();(P/'candidate.json').write_bytes(cr)
ren={n:'n_'+n for n in w};rep=lambda x:'shift_'+x if isinstance(x,str) and x in ren else x
ns=[['shift_'+n,'+',ren[n],1] for n in w]+[[n,o,rep(a),rep(b)] for n,o,a,b in rows]
n={'scope':'Natural-variable shifted external candidate; Lean endpoint open.','positive_parent_sha256':hashlib.sha256(cr).hexdigest(),'witnesses':[ren[n] for n in w],'fixed_numerals':p['fixed_numerals'],'source':ns,'output':c['output'],'operations':len(ns)}
(P/'natural-candidate.json').write_text(json.dumps(n,indent=2)+'\n')
