#!/usr/bin/env python3
"""Shift only witnesses not forced positive by the square constraints."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;D=P.parents[1]
r=(D/'research/adaptive-aq17-factored-root94/candidate.json').read_bytes();assert hashlib.sha256(r).hexdigest()=='7f9a6af2c44f1e9b6c763c9dd38cc4a3beb79d5dcd159539dc7275873e67c71a'
p=json.loads(r);forced={'firstQuotient','mainQuotient','vValueVariable'}
ren={x:'n_'+x for x in p['witnesses']};shifted={x:'shift_'+x for x in p['witnesses'] if x not in forced}
rep=lambda x:shifted.get(x,ren.get(x,x)) if isinstance(x,str) else x
rows=[['shift_'+x,'+',ren[x],1] for x in p['witnesses'] if x not in forced]+[[n,o,rep(a),rep(b)] for n,o,a,b in p['source']]
c={'scope':'External natural zero-map candidate; Lean transfer and iPRA endpoint open.','positive_parent_sha256':hashlib.sha256(r).hexdigest(),'forced_unshifted':sorted(forced),'witnesses':[ren[x] for x in p['witnesses']],'fixed_numerals':p['fixed_numerals'],'source':rows,'output':p['output'],'operations':len(rows)}
(P/'candidate.json').write_text(json.dumps(c,indent=2)+'\n')
