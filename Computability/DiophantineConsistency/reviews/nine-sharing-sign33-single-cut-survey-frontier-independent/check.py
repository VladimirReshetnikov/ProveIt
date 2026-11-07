#!/usr/bin/env python3
import json,hashlib
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign33-single-cut-substitution-survey';O=D/'research/nine-sharing-quartic65-sign33-candidate/seed.json';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(P/'check.py')=='185bb574334e138a506881aacaadf91becefd97cd59c47519c3c2a9d9bb63b82'
assert sha(P/'result.json')=='6a8a398f49b61b4b09b562922d4e242276ce19e5b4b885caee0c0fb509286ab2'
assert sha(O)=='a8cd4d01962b9380065ebbd3d7b75db3ffcadf18969099398bd151c4e2219e75'
s=json.loads(O.read_bytes());res=json.loads((P/'result.json').read_bytes());rr=s['residuals'];assert len(rr)==24
# Assign a degree weight to each variable, then evaluate every untouched AST;
# this is independent of constructing the transformed AST itself.
def degree(t,weights):
 if t[0]=='var':return weights.get(t[1],1)
 if t[0] in ('num','port'):return 0
 assert t[0] in ('add','sub','mul')
 a,b=degree(t[1],weights),degree(t[2],weights)
 return a+b if t[0]=='mul' else max(a,b)
out=[]
for j,r in enumerate(rr):
 if r['kind'] not in ('positive','signed'):continue
 t=r['expr'];assert t[0]=='sub' and t[1][0]=='var';idx=t[1][1]; rhs=t[2]
 def occurs(t):return (t[0]=='var' and t[1]==idx) or (t[0] not in ('var','num','port') and (occurs(t[1]) or occurs(t[2])))
 assert not occurs(rhs)
 weights={idx:degree(rhs,{})}; ds=[(x['gate'],degree(x['expr'],weights)) for i,x in enumerate(rr) if i!=j];m=max(d for _,d in ds)
 out.append({'gate':r['gate'],'kind':r['kind'],'eliminated_full_coordinate':idx,'syntactic_max_residual_degree':m,'syntactic_seed_degree_upper':2*m,'max_degree_residuals':[n for n,d in ds if d==m]})
assert len(out)==19 and {x['eliminated_full_coordinate'] for x in out}==set(range(15,34))
assert out==res['cases'] and all(x['syntactic_max_residual_degree'] in (3,4) for x in out)
print(json.dumps({'status':'PASS_SOURCE_ONLY','cases':len(out),'coordinate_range':'15..33','degree3_cases':sum(x['syntactic_max_residual_degree']==3 for x in out),'degree4_cases':sum(x['syntactic_max_residual_degree']==4 for x in out),'scope':'degree recursion of displayed single-cut AST substitutions only; no algebraic simplification or semantic lower bound'},indent=2,sort_keys=True))
