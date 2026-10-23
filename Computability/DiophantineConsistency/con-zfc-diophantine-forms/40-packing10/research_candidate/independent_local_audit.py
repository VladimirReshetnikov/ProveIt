#!/usr/bin/env python3
"""Compare the generalized occupied decoder with the original 943-tile language."""
import importlib.util,json
from pathlib import Path
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('candidate',HERE/'build_factorized.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
spec=importlib.util.spec_from_file_location('source',HERE/'coefficients__build_coefficients.py')
s=importlib.util.module_from_spec(spec);spec.loader.exec_module(s)
source,_=s.language()
right=sorted({t for q,b,v,d,t in m.ROWS if d==1})
left=sorted({t for q,b,v,d,t in m.ROWS if d==-1})
hor={0:0,1:1,2:2,3:3,4:4,5:5}
hor.update({j+6:256+q for j,q in enumerate(right)})
hor.update({j+6+len(right):512+q for j,q in enumerate(left)})
vert={0:0,1:1,434:2,435:3,436:4,437:5,438:6}
vert.update({2*(q+1)+b:512+2*q+b for q in range(216) for b in (0,1)})
old={tuple([hor[t[0]],vert[t[1]],hor[t[2]],vert[t[3]]]) for t in source}
data=m.recipe();expanded=set();constructive=0
for i,t in enumerate(data['tiles']):
    if i==data['ir']:
        variants=[((256+q,b,0,512+2*q+b),q,0,b) for q in range(256) for b in (0,1)]
    elif i==data['il']:
        variants=[((0,b,512+q,512+2*q+b),0,q,b) for q in range(256) for b in (0,1)]
    else:variants=[(t,0,0,0)]
    for tile,qr,ql,b in variants:
        value=data['ce'][i]
        value+=sum(data['ce'][m.QR[j]] for j in range(8) if qr>>j&1)
        value+=sum(data['ce'][m.QL[j]] for j in range(8) if ql>>j&1)
        if b:value+=data['ce'][m.BSYM]
        value+=sum(data['ce'][m.OFFSETS[s]+j] for s,x in enumerate(tile)
                   for j in range(11) if (x+1024)>>j&1)
        value+=sum(data['ce'][e] for e in m.ANCHORS)
        assert value&data['mu']==0,(i,tile)
        expanded.add(tile);constructive+=1
assert len(old)==943 and len(expanded)==1479 and old<=expanded
east={t[2] for t in expanded};west={t[0] for t in expanded}
extra=expanded-old
assert len(extra)==536
for w,n,e,so in extra:
    assert (w!=0 and w not in east) or (e!=0 and e not in west)
# All other tiles agree exactly with the original literal Wang language after relabelling.
trimmed={t for t in expanded if t[0] in east and t[2] in west}
assert trimmed==old-{(5,0,0,0)} # the inherited forbidden tile is likewise locally impossible.
print(json.dumps(dict(status='PASS',original_tiles=len(old),selector_modes=len(data['tiles']),
                      occupied_expansion=len(expanded),constructive_witnesses=constructive,
                      impossible_extras=len(extra),trimmed_tiles=len(trimmed)),indent=2))
