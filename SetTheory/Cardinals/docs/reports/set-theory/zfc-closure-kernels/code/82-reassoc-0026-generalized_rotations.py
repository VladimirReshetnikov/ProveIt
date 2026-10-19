import sys,json,time
from functools import cache
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent));import rotation_candidate as m
T=m.T;nodes=m.nodes;h=m.h
bound=h.bounder(nodes)
pure={q for q,b in T if all(T[q,b][:2]==(b,'R') for b in (0,1))}
@cache
def fp(n):return tuple(fp(int(e.split()[1])) if e.startswith('ENode ') else e for e in nodes[n])
fps={q:{fp(n) for n in ns} for q,ns in m.q2nodes.items()}
uniform={q:next(iter(v)) for q,v in fps.items() if len(v)==1}
qb={q:bound('ENode '+str(next(iter(m.q2nodes[q])))) for q in uniform}
lookup={(T[q,0][2],T[q,1][2]):q for q in pure}
recipes=[]
for q in sorted(pure&set(uniform)):
 for side in (0,1):
  r=T[q,side][2]
  if r not in pure&set(uniform):continue
  if side==0:a,b,c=T[r,0][2],T[r,1][2],T[q,1][2]
  else:a,b,c=T[q,0][2],T[r,0][2],T[r,1][2]
  if not all(x in uniform for x in (a,b,c)):continue
  if qb[a][0] or qb[c][1]:continue
  need=(b,c) if side==0 else (a,b)
  if need in lookup:
   s=lookup[need];new=(a,s) if side==0 else(s,c)
   recipes.append((q,r,side,a,b,c,s,lookup.get(new),[qb[x] for x in (a,b,c)]))
print('RECIPES',len(recipes),recipes,flush=True)
(m.HERE/'rotation_candidates/generalized_one_step.json').write_text(json.dumps(dict(domain='one literal associativity rotation whose needed new pair is an existing pure R state; uniform pure-R source map; A break-bound0 and C continue-bound0',recipes=recipes,recipe_count=len(recipes)),indent=2)+'\n')
# Only new domains, previous first4wereclosedtested.
for q,r,side,a,b,c,s,complete,bb in recipes:
 if (q,r) in [(178,208),(190,99),(219,178),(226,193)]:continue
 # Extend exact fp occurrences for semantic consistency.
 m.q2nodes[q]={n for n in nodes if fp(n)==uniform[q]}
 m.recipe(q,r,side,a,b,c,s)
