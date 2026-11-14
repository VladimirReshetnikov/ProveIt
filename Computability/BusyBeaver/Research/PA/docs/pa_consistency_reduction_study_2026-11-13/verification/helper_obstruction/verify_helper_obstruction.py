#!/usr/bin/env python3
"""Reconstruct the frozen direct-selector folding LP and check its exact dual.

Python standard library only. This is a lower bound for one explicitly limited
state-sharing template, not for arbitrary Turing machines or alternative grammars.
"""
from pathlib import Path
from collections import defaultdict
from fractions import Fraction
import hashlib,itertools,json

if not __debug__:
    raise SystemExit('Run without -O or PYTHONOPTIMIZE; assertions check the certificate.')

HERE=Path(__file__).resolve().parent
cert=json.loads((HERE/'helper_lp_certificate.json').read_text())
raw=(HERE/'primary201.native.tm').read_bytes()
assert hashlib.sha256(raw).hexdigest()==cert['raw_table_sha256']
rows={}
for line in raw.decode().splitlines():
    if not line or line.startswith('#'):continue
    q,b,w,d,n=line.split();key=int(q),int(b)
    assert key not in rows and d in ('L','R')
    rows[key]=int(w),d=='R',int(n)
controls=sorted({q for q,b in rows})
readers=cert['reader_states']
assert len(controls)==201 and len(rows)==402 and len(readers)==67
assert readers==[q for q in controls if q>=2000]
assert all((q,b)in rows for q in controls for b in (0,1))
incoming=defaultdict(set)
for (q,b),(w,d,n) in rows.items():
    if n in readers:
        assert w==b and d
        incoming[n].add(b)
left=[q for q in readers if incoming[q]=={0}]
right=[q for q in readers if incoming[q]=={1}]
providers=[defaultdict(list),defaultdict(list)]
reverse=[defaultdict(set),defaultdict(set)]
for q in controls:
    for b in (0,1):reverse[b][rows[q,b]].add(q)
    z,o=rows[q,0],rows[q,1]
    if z[:2]==(0,True) and o[:2]==(1,True) and z[2] in controls and o[2] in controls:
        for b in (0,1):providers[b][rows[z[2],b],rows[o[2],b]].append((q,z[2],o[2]))
requirements={};allhelpers=set()
for a,b in itertools.product(left,right):
    need=[]
    for bit in (0,1):
        if rows[a,bit]==rows[b,bit] or any(not {a,b}&set(p) for p in providers[bit].get((rows[a,bit],rows[b,bit]),[])):
            need.append(None)
        else:
            possible={(u,v) for u in reverse[bit][rows[a,bit]] for v in reverse[bit][rows[b,bit]] if not {a,b}&{u,v}}
            need.append(possible);allhelpers.update(possible)
    requirements[a,b]=need
helpers=sorted(allhelpers)
edges=[pair for pair,need in requirements.items() if all(item is None or item for item in need)]
assert helpers==list(map(tuple,cert['helpers']))
assert edges==list(map(tuple,cert['fold_pairs']))
nh,ne=len(helpers),len(edges)
index={h:i for i,h in enumerate(helpers)}
constraints=[];bounds=[]
for q in left+right:
    constraints.append({nh+i:1 for i,pair in enumerate(edges) if q in pair});bounds.append(1)
for i,pair in enumerate(edges):
    for needed in requirements[pair]:
        if needed is not None:
            row={nh+i:1};row.update({index[h]:-1 for h in needed})
            constraints.append(row);bounds.append(0)
objective=[1]*nh+[-1]*ne
assert objective==cert['objective']
assert constraints==[{int(j):v for j,v in d.items()} for d in cert['constraints']]
assert bounds==cert['upper_bounds']
y=list(map(Fraction,cert['dual_constraints']))
z=list(map(Fraction,cert['dual_upper_variables']))
assert len(y)==len(constraints) and len(z)==len(objective)
assert all(t<=0 for t in y+z)
column=[Fraction(0) for _ in objective]
for row,weight in zip(constraints,y):
    for j,v in row.items():column[j]+=v*weight
assert all(column[j]+z[j]<=objective[j] for j in range(len(objective)))
bound=sum(b*t for b,t in zip(bounds,y))+sum(z)
assert bound==-7 and Fraction(cert['lower_bound'])==bound
assert 201+bound==cert['final_state_lower_bound']==194
print(json.dumps({'verified':True,'raw_states':201,'reader_states':67,
 'helper_types':nh,'possible_disjoint_pair_types':ne,'linear_constraints':len(constraints),
 'exact_objective_lower_bound':str(bound),'exact_final_state_lower_bound':194,
 'scope':cert['scope']},indent=2))
