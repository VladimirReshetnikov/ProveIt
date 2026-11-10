#!/usr/bin/env python3
"""Search nonnegative single-variable substitutions and rank the resulting syntactic degree bounds.

Pure syntax/degree exploration on the pinned sign26 AST. This does not prove
model transfer, exact algebraic degree, or bind external AST to Lean.
"""
from functools import lru_cache
from hashlib import sha256
import json
from pathlib import Path
p=Path(__file__).resolve().parent.parent/'nine-sharing-sign23-octic-delta-candidate/seed.json'
raw=p.read_bytes();assert sha256(raw).hexdigest()=='ee6079ea26dd120fab39789f83034947c18e0c8806945a1fc75fca62e1c65d41';seed=json.loads(raw)
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
assert seed['witness_count']==23 and max(degree(e) for _,_,e in rows)==4
records=[]
def visit(rows,path,remaining):
 options=[]
 for gate,i,v in eligible(rows):
  nxt=tuple((g,k,subst(e,i,v)) for g,k,e in rows if g!=gate)
  d=max(degree(e) for _,_,e in nxt)
  options.append({'gate':gate,'old_coordinate':i,'residual_degree_bound':d})
  if len(path)<5:
   visit(nxt,path+[gate],remaining-1)
 records.append({'eliminated':path,'witness_count':remaining,
                 'residual_degree_bound':max(degree(e) for _,_,e in rows),
                 'options':options})
visit(rows,[],23)
counts=sorted({x['witness_count'] for x in records})
frontier=[]
for n in counts:
 subset=[x for x in records if x['witness_count']==n]
 best=min(x['residual_degree_bound'] for x in subset)
 frontier.append({'witness_count':n,'best_residual_degree_bound':best,
                  'sequences':[x['eliminated'] for x in subset if x['residual_degree_bound']==best]})
print(json.dumps({'status':'PASS_FINITE_SYNTACTIC_SEARCH','source_sha256':sha256(raw).hexdigest(),
 'scope':'positive direct-variable gates only, syntactic degree, original labels, no model/Lean/exact-degree claim',
 'states':len(records),'frontier':frontier,'all_states':records},sort_keys=True,indent=2))
