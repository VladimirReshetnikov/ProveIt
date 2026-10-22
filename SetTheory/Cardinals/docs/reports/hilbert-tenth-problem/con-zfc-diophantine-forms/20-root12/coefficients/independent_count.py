"""Center-class census independent of the four-tuple predicate."""
import collections,json
from pathlib import Path
root=Path(__file__).resolve().parent
rows=json.loads((root/'sources/k215_transitions.json').read_text())['transitions']
left=collections.defaultdict(set);right=collections.defaultdict(set)
for q,b,w,d,t in rows:(right if d==1 else left)[t].add(w)
counts={};detail={}
for b in(0,1):
 hleft=sum(bool(right[q]) or b in left[q] for q in range(216))
 hright=sum(bool(left[q]) or b in right[q] for q in range(216))
 normal=4+4*(hleft+hright)
 end=4+4*int(bool(right[215]) or b in left[215])+4*int(bool(left[215]) or b in right[215])
 collar=8 if b==0 else 0;excluded=int(b==0)
 counts['headless'+str(b)]=normal+end+collar+excluded
 detail[str(b)]=dict(left_heads=hleft,right_heads=hright,normal=normal,end=end,collar=collar,excluded=excluded)
counts['working_heads']=2*sum(sum(l in right[q] or r in left[q] for l in(0,1) for r in(0,1)) for q in range(215))
counts['halt_heads']=4*sum(l in right[215] or r in left[215] for l in(0,1) for r in(0,1))
counts.update(initial_L=4,initial_Q=1,initial_R=4,vertical=9,horizontal=5)
assert counts=={'headless0':1457,'headless1':1484,'working_heads':1122,'halt_heads':8,'initial_L':4,'initial_Q':1,'initial_R':4,'vertical':9,'horizontal':5},counts
assert sum(counts.values())==4094
out=dict(status='PASS',total=sum(counts.values()),center_counts=counts,headless_detail=detail,scope='Closed center-class count independently reproduces the direct finite alphabet cardinality.')
(root/'independent_count.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
