#!/usr/bin/env python3
"""Construct the unshift-s probe only; not a new consistency candidate."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;D=P.parents[1]
b=(D/'research/ordinary13-natural-residue-forced88-degree60/candidate.json').read_bytes();assert hashlib.sha256(b).hexdigest()=='cb488cb849c08c11d159f8805fdd7664c6472cbd41cefadc530e21060a5a1dd2'
p=json.loads(b);assert ['shift_s','+','n_s',1] in p['source']
def sub(x):return 'n_s' if x=='shift_s' else x
rows=[[n,o,sub(a),sub(c)] for n,o,a,c in p['source'] if n!='shift_s']
probe={'scope':'Boundary probe only; no consistency equivalence asserted.','parent_sha256':hashlib.sha256(b).hexdigest(),'domain':p['domain'],'witnesses':p['witnesses'],'fixed_numerals':p['fixed_numerals'],'source':rows,'output':p['output'],'operations':len(rows)}
(P/'probe.json').write_text(json.dumps(probe,indent=2)+'\n')
