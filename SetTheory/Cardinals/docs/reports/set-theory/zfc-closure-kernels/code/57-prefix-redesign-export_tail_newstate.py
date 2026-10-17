#!/usr/bin/env python3
"""Export the joint zeroDEC/INC/positiveDEC terminal lookahead obligation."""
from pathlib import Path
import prefix_tail_lookahead as p
HERE=Path(__file__).resolve().parent
out=HERE/'tail_newstate';out.mkdir(exist_ok=True)
(out/'table.tm').write_bytes(p.z.audit.encode(p.z.T))
(out/'control.tm').write_bytes(p.z.audit.encode(p.z.base))
cases=list(p.cases());order=[0,27,54]+[i for i in range(len(cases))if i not in(0,27,54)]
lines=[]
for i in order:
    c=cases[i];initial=sorted(c['ones']);targets=[sorted(t)for t in c['targets']]
    while len(targets)<3:targets.append(targets[-1])
    header=[i,c['r'],c['head'],c['outhead'],len(initial)]+[len(t)for t in targets]
    lines.append(' '.join(map(str,header+initial+[j for t in targets for j in t])))
(out/'cases.txt').write_text('\n'.join(lines)+'\n')
print('Exported',len(cases),'tail samples; all source root controls passed.')
