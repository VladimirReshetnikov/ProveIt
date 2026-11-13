#!/usr/bin/env python3
"""Search nonnegative single-variable substitutions within the decic bound.

Pure syntax/degree exploration on the pinned sign26 AST. This does not prove
model transfer, exact algebraic degree, or bind external AST to Lean.
"""
from functools import lru_cache
from hashlib import sha256
import json
from pathlib import Path
p=Path(__file__).resolve().parent.parent/'nine-sharing-sign26-sextic-gap-congruence-candidate/seed.json'
raw=p.read_bytes();assert sha256(raw).hexdigest()=='36efa7dd3b2ea06d210b8975db2cbfc4f7494549c87204ada18747a720cb1f25';seed=json.loads(raw)
def freeze(x): return tuple(freeze(i) if isinstance(i,list) else i for i in x)
def nonnegative(e):
 if e[0]=='num':return type(e[1]) is int and e[1]>=0
 if e[0] in ('var','port'):return True
 return e[0] in ('add','mul') and nonnegative(e[1]) and nonnegative(e[2])
@lru_cache(None)
def degree(e):
 if e[0]=='var':return 1
 if e[0] in ('num','port'):return 0
 a,b=degree(e[1]),degree(e[2]);return a+b if e[0]=='mul' else max(a,b)
@lru_cache(None)
def occurs(e,i):
 if e[0]=='var':return e[1]==i
 if e[0] in ('num','port'):return False
 return occurs(e[1],i) or occurs(e[2],i)
@lru_cache(None)
def subst(e,i,v):
 if e[0]=='var':return v if e[1]==i else e
 if e[0] in ('num','port'):return e
 return (e[0],subst(e[1],i,v),subst(e[2],i,v))
def eligible(rows):
 for gate,kind,e in rows:
  if kind!='positive' or e[0]!='sub' or e[1][0]!='var':continue
  i=e[1][1];v=e[2]
  if i==0 or occurs(v,i) or not nonnegative(v):continue
  yield gate,i,v
rows=tuple((r['gate'],r['kind'],freeze(r['expr'])) for r in seed['residuals'])
assert seed['witness_count']==26 and max(degree(e) for _,_,e in rows)==3
records=[]
def visit(rows,path,remaining):
 options=[]
 for gate,i,v in eligible(rows):
  nxt=tuple((g,k,subst(e,i,v)) for g,k,e in rows if g!=gate)
  d=max(degree(e) for _,_,e in nxt)
  options.append({'gate':gate,'old_coordinate':i,'residual_degree_bound':d})
  if d<=5 and len(path)<6:
   visit(nxt,path+[gate],remaining-1)
 records.append({'eliminated':path,'witness_count':remaining,
                 'residual_degree_bound':max(degree(e) for _,_,e in rows),
                 'options':options})
visit(rows,[],26)
minimum=min(x['witness_count'] for x in records)
print(json.dumps({'status':'PASS_FINITE_SYNTACTIC_SEARCH','source_sha256':sha256(raw).hexdigest(),
 'scope':'positive direct-variable gates only, bound degree<=5, original variable labels, no model/Lean/exact-degree claim',
 'states':len(records),'minimum_witnesses':minimum,
 'best':[r for r in records if r['witness_count']==minimum],
 'states_at_each_count':{str(n):sum(r['witness_count']==n for r in records) for n in sorted({r['witness_count'] for r in records})},
 'all_states':records},sort_keys=True,indent=2))
