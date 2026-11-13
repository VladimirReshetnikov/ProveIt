#!/usr/bin/env python3
"""Exhaustive syntactic one-cut substitutions of the fixed 33 residual AST."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];raw=(D/'research/nine-sharing-quartic65-sign33-candidate/seed.json').read_bytes();assert hashlib.sha256(raw).hexdigest()=='a8cd4d01962b9380065ebbd3d7b75db3ffcadf18969099398bd151c4e2219e75'
s=json.loads(raw);rows=s['residuals'];assert len(rows)==24 and s['jones_witness_count']==33
def vars_of(t):
 if t[0]=='var':return {t[1]}
 if t[0] in ('num','port'):return set()
 return vars_of(t[1])|vars_of(t[2])
def degree(t):
 if t[0] in ('num','port'):return 0
 if t[0]=='var':return 1
 assert t[0] in ('add','sub','mul')
 a,b=degree(t[1]),degree(t[2]);return a+b if t[0]=='mul' else max(a,b)
def replace(t,idx,rhs):
 if t[0]=='var':return rhs if t[1]==idx else t
 if t[0] in ('num','port'):return t
 return [t[0],replace(t[1],idx,rhs),replace(t[2],idx,rhs)]
out=[]
for i,row in enumerate(rows):
 expr=row['expr']
 if row['kind'] not in ('positive','signed'):continue
 assert expr[0]=='sub' and expr[1][0]=='var';idx=expr[1][1];rhs=expr[2];assert idx not in vars_of(rhs)
 transformed=[(other['gate'],degree(replace(other['expr'],idx,rhs))) for j,other in enumerate(rows) if i!=j];maxdeg=max(d for _,d in transformed)
 out.append({'gate':row['gate'],'kind':row['kind'],'eliminated_full_coordinate':idx,'syntactic_max_residual_degree':maxdeg,'syntactic_seed_degree_upper':2*maxdeg,'max_degree_residuals':[n for n,d in transformed if d==maxdeg]})
assert len(out)==19 and all(x['syntactic_max_residual_degree']>2 for x in out)
print(json.dumps({'status':'PASS_EXTERNAL_SINGLE_CUT_SYNTACTIC_SURVEY','source_sha256':hashlib.sha256(raw).hexdigest(),'cases':out,'case_count':len(out),'quartic_syntactic_cases':0,'scope':'Exactly one displayed cut-defining residual and its coordinate are substituted into the remaining displayed residuals; no algebraic simplification, alternate encoding, actual degree lower bound, sign proof, Lean theorem or global optimality.'},indent=2,sort_keys=True))
