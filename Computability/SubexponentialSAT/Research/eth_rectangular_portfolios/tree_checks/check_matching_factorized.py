"""Author-written independent exact test harness; no archive imports."""
import json,random
from matching_factorized import solve
rng=random.Random(20261027)
cases=[[]]
for mask in range(16):cases.append([(a,b) for a in range(2) for b in range(2) if mask&(1<<(2*a+b))])
cases += [[(0,0)]*m for m in range(1,6)]
for _ in range(36):
    L=rng.randrange(1,5);R=rng.randrange(1,5)
    cases.append([(rng.randrange(L),rng.randrange(R)) for _ in range(rng.randrange(1,10))])
checks=0;trace_values=0;candidate_values=0
for edges in cases:
    for Q in [1,2,3,4]:
        for eta in [1,2,5]:
            outputs=[solve(edges,Q,eta,method=m,all_candidates=True) for m in ['oracle','dense','factorized','sparse']]
            if any(out!=outputs[0] for out in outputs[1:]):raise ArithmeticError((edges,Q,eta))
            checks+=1;trace_values+=len(outputs[0]['trace']);candidate_values+=sum(map(len,outputs[0]['candidates']))
# More large cases against maintained dense reference, not the slow literal oracle.
large=0
for Q in [2,4,8,12]:
    for eta in [1,4]:
        for _ in range(4):
            edges=[(rng.randrange(12),rng.randrange(10)) for _ in range(36)]
            a=solve(edges,Q,eta,method='dense',all_candidates=True)
            b=solve(edges,Q,eta,method='factorized',all_candidates=True)
            c=solve(edges,Q,eta,method='sparse',all_candidates=True)
            if a!=b or b!=c:raise ArithmeticError(('large',Q,eta))
            large+=1
print(json.dumps({'oracle_comparisons':checks,'methods':['oracle','dense','factorized','sparse'],'large_dense_comparisons':large,'selected_trace_values':trace_values,
'all_candidate_values':candidate_values,'scope':'Self-authored literal conditional product oracle and maintained dense reference; no archive code imported/executed.'},indent=2))
