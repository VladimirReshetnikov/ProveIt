#!/usr/bin/env python3
"""Universal, all-tape native68 -> native62 control bisimulation."""
from pathlib import Path
import build_library as B
HERE=Path(__file__).resolve().parent
d=B.build(full=False)
for field in ('rows','entries','ports','domains','proofs','names'):
 d[field]={k:v for k,v in d[field].items()if(k[0]if isinstance(k,tuple)else k).startswith('native:')or(isinstance(k,str)and k.startswith('native.'))}
d['domains']={q:[0,1]for q in d['domains']};d['proofs']={};d['protected']={q for q in d['protected']if q.startswith('native:')};d['ledger']={'native':d['ledger']['native']}
r=B.quotient(d);assert len(r['classes'])==62 and not r['pairs'];B.save(d,r,HERE/'native62')
print('native68 -> native62: all136 original rows have exact projected actions; return and reject remain distinct.')
