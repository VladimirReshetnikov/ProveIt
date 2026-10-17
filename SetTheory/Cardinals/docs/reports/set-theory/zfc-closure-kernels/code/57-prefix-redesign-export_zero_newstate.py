#!/usr/bin/env python3
"""Export exact restore-entry cases for one-state zero-decrement repair.

The no-spare subset is the required invariant for the new prefix initializer.
Nonzero spare cases are exported separately as optional stronger controls.
"""
import json,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'compression'))
import prefix_zero_repair as z
out=HERE/'zero_newstate';out.mkdir(exist_ok=True)
(out/'table.tm').write_bytes(z.audit.encode(z.T))
(out/'control.tm').write_bytes(z.audit.encode(z.base))
cases=list(z.inputs())
for name,chosen in [('cases',[c for c in cases if not c['spares']]),('extra_cases',cases)]:
    rows=[]
    for i,c in enumerate(chosen):
        initial=sorted(c['ones']);targets=[sorted(t) for t in c['targets']]
        header=[i,c['r'],c['head'],c['outhead'],len(initial)]+[len(t) for t in targets]
        rows.append(' '.join(map(str,header+initial+[p for t in targets for p in t])))
    (out/f'{name}.txt').write_text('\n'.join(rows)+'\n')
print(json.dumps(dict(no_spare_samples=sum(not c['spares'] for c in cases),extra_samples=len(cases))))
out75=HERE/'zero_newstate75';out75.mkdir(exist_ok=True)
for filename in ('table.tm','control.tm','cases.txt','extra_cases.txt'):
    (out75/filename).write_bytes((out/filename).read_bytes())
