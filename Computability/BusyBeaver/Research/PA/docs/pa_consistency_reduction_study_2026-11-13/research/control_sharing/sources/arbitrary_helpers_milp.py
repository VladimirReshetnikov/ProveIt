#!/usr/bin/env python3
"""Research search; relative-path packaging adaptation, algorithm unchanged."""
from pathlib import Path
if not __debug__:
    raise SystemExit("Assertions are required; do not use -O or PYTHONOPTIMIZE.")
exec(Path(__file__).with_name('two_helpers.py').read_text().split('\ncount=0;t0=time.time()')[0])
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import lil_matrix
edges=[(a,b) for (a,b),rr in requirements.items() if all(z is None or z for z in rr)]
nh=len(allhelpers);ne=len(edges);hindex={h:i for i,h in enumerate(allhelpers)}
constraints=[];lb=[];ub=[]
for q in list(L)+list(R):
 constraints.append({nh+j:1 for j,e in enumerate(edges) if q in e});lb.append(-np.inf);ub.append(1)
for j,e in enumerate(edges):
 for req in requirements[e]:
  if req is not None:
   d={nh+j:1};d.update({hindex[h]:-1 for h in req});constraints.append(d);lb.append(-np.inf);ub.append(0)
A=lil_matrix((len(constraints),nh+ne))
for i,d in enumerate(constraints):
 for j,v in d.items():A[i,j]=v
obj=np.array([1.]*nh+[-1.]*ne)
print('MILP',nh,ne,len(constraints),flush=True)
res=milp(obj,integrality=np.ones(nh+ne),bounds=Bounds(0,1),constraints=LinearConstraint(A.tocsr(),lb,ub),options={'time_limit':300,'mip_rel_gap':0.0})
print('RESULT',res,flush=True)
record={k:(v.tolist() if hasattr(v,'tolist') else v)for k,v in res.items()}
if res.x is not None:
 hs=[h for i,h in enumerate(allhelpers) if res.x[i]>.5];es=[e for j,e in enumerate(edges) if res.x[nh+j]>.5]
 record.update(helpers=hs,fold_pairs=es,final_lower_bound=len(qs)+len(hs)-len(es))
 print('HELPERS',hs,'EDGES',es,'FINAL',record['final_lower_bound'],flush=True)
 table=dict(rows)
 for j,(u,v) in enumerate(hs):
  table[2400+j,0]=(0,True,u);table[2400+j,1]=(1,True,v)
 ops=[o for o in c.opportunities_fast(table,shape) if(o[0],o[1])in es]
 sol,n=solve(ops,table,len(es));record.update(compatible=bool(sol),folds=sol)
 print('COMPATIBLE',bool(sol),flush=True)
(OUTPUT_DIR/'arbitrary_helpers_milp.json').write_text(json.dumps(record,indent=2))
