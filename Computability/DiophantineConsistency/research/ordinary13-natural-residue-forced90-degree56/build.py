#!/usr/bin/env python3
"""Mixed natural shift of residue-first82 with five unshifted inputs."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;D=P.parents[1]
b=(D/'research/ordinary13-residue-first82/candidate.json').read_bytes();assert hashlib.sha256(b).hexdigest()=='bb90faa3815c5ff46f5fdbf41c2d001790d565baa17d97c79514c33fa928f1d2'
p=json.loads(b);forced={'J','f','y','X','gamma'};ren={x:'n_'+x for x in p['witnesses']};shift={x:'shift_'+x for x in p['witnesses'] if x not in forced}
rep=lambda x:shift.get(x,ren.get(x,x)) if isinstance(x,str) else x
rows=[['shift_'+x,'+',ren[x],1] for x in p['witnesses'] if x not in forced]+[[n,o,rep(a),rep(b)] for n,o,a,b in p['source']]
c={'scope':'External natural zero-map candidate; Lean transfer and iPRA endpoint open.','positive_parent_sha256':hashlib.sha256(b).hexdigest(),'domain':'nonnegative integers','forced_unshifted':sorted(forced),'witnesses':[ren[x] for x in p['witnesses']],'fixed_numerals':p['fixed_numerals'],'source':rows,'output':p['output'],'operations':len(rows)}
(P/'candidate.json').write_text(json.dumps(c,indent=2)+'\n')
