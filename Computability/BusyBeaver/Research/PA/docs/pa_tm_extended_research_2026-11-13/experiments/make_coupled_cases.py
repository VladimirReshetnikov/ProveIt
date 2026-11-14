"""Generate coupled-selector layouts from the exported local contexts."""
import json
from pathlib import Path
labs=json.loads(Path('experiments/labels.json').read_text())
af=iter(map(int,Path('experiments/actions.dat').read_text().split()))
opts={}
for q in range(len(labs)-1):
    for b in (0,1):
        opts[q,b]={tuple(next(af) for _ in range(3)) for j in range(next(af))}
ed={tuple(list(map(int,l.split()))[:5])
    for l in Path('experiments/general_selector.log').read_text().splitlines()}
states=list(map(int,Path('experiments/contexts.dat').read_text().splitlines()[1].split()))
cases=set()
for e in ed:
    for nq in states:
        if nq in e[:2]: continue
        bit=1 if e[2]==1 else 0
        common=opts[e[0],bit]&opts[e[1],bit] if e[2]!=3 else {(-1,-1,-1)}
        for co in common: cases.add((*e,nq,*co))
with Path('experiments/coupled_cases.dat').open('w') as f:
    print(len(cases),file=f)
    for c in sorted(cases,key=lambda c:(min(c[:2])<134,c)):
        print(*c,file=f)
print(f'Generated {len(cases)} coupled layouts')
