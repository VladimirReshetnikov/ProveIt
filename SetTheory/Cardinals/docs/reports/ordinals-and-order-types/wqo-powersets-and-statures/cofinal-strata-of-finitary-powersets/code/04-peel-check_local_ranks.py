"""Independent exact finite-rank tests for CNF refinement and local ranks."""
import itertools
import json
from pathlib import Path
from ordinals import Ordinal as O, OMEGA, ZERO, ONE
from persistent_height import System, closure, bits, refine_capacities, exact_point_rank
from verify import posets

ROOT=Path(__file__).resolve().parents[1]
counts={'finite_systems':0,'finite_point_ranks':0,'symbolic_examples':0}

# Finite coordinate systems have exactly enumerable posets and integer ranks.
for n in range(4):
    for le in posets(n):
        for active in itertools.product(range(4),repeat=n):
            for lengths in [(1,2),(2,3)]:
                s=System(le,list(active),{0:O.nat(lengths[0]),1:O.nat(lengths[1])})
                try:
                    s.validate(pure=False)
                except ValueError:
                    continue
                points=[]
                for i,mask in enumerate(active):
                    qs=list(bits(mask))
                    for values in itertools.product(*(range(lengths[q]) for q in qs)):
                        points.append((i,dict(zip(qs,values))))
                def less(a,b):
                    i,x=a; j,y=b
                    return (a!=b and bool(le[i]>>j&1) and
                            all(x[q]<=y[q] for q in x.keys() & y.keys()))
                # Repeated removal of minimal remaining elements is independent
                # of both ordinal algorithms and of the refinement construction.
                ranks={}
                remaining=set(range(len(points)))
                while remaining:
                    ready=[j for j in remaining if not any(less(points[i],points[j]) for i in remaining)]
                    assert ready
                    for j in ready:
                        ranks[j]=max([0]+[ranks[i]+1 for i in ranks if less(points[i],points[j])])
                    remaining.difference_update(ready)
                refined,_=refine_capacities(s)
                refined.validate()
                h,_=refined.height_dp(False)
                assert h==O.nat(max(ranks.values(),default=-1)+1)
                counts['finite_systems']+=1
                for j,(i,x) in enumerate(points):
                    r=exact_point_rank(s,i,{q:O.nat(v) for q,v in x.items()})
                    assert r==O.nat(ranks[j]),(s,i,x,r,ranks[j])
                    counts['finite_point_ranks']+=1

symbolic=[]
# In a finite product of ordinal chains the point rank is natural sum;
# this regression does not assume our total-height formula.
values=[ZERO,ONE,O.nat(3),OMEGA,OMEGA+ONE,OMEGA.right_times(2)+O.nat(2)]
s=System([1],[3],{0:O.power(O.nat(2)),1:O.power(O.nat(2))})
for x,y in itertools.product(values,repeat=2):
    r=exact_point_rank(s,0,{0:x,1:y})
    assert r==x.natural_sum(y)
    symbolic.append({'coordinates':[str(x),str(y)],'rank':str(r)})
    counts['symbolic_examples']+=1
# A label disappears below a coordinate-free greatest state.
s=System(closure(2,[(0,1)]),[1,0],{0:OMEGA})
assert exact_point_rank(s,1,{})==OMEGA
counts['symbolic_examples']+=1
report={'status':'PASS','counts':counts,'product_examples':symbolic,
        'scope':'Finite exact point ranks plus stated symbolic regressions; not a proof-assistant check.'}
(ROOT/'data/local_rank_verification.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':'PASS','counts':counts},indent=2))
