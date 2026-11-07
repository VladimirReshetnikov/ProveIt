#!/usr/bin/env python3
"""Finite direct-cut survey with one precise monic q³ remainder; not a lower bound."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;raw=(P.parent/'nine-sharing-sign26-sextic-gap-congruence-candidate/seed.json').read_bytes();assert hashlib.sha256(raw).hexdigest()=='36efa7dd3b2ea06d210b8975db2cbfc4f7494549c87204ada18747a720cb1f25';s=json.loads(raw)
V=lambda i:['var',i];N=lambda i:['num',i];aa=['mul',['port','beta'],['add',V(1),N(1)]]
def subst(t,k,r):
 if t[0]=='var':return r if t[1]==k else t
 if t[0] in ('port','num'):return t
 assert t[0] in ('add','sub','mul') and len(t)==3
 return [t[0],subst(t[1],k,r),subst(t[2],k,r)]
def add(x,y,sgn=1):
 z=x.copy()
 for k,v in y.items():z[k]=z.get(k,0)+sgn*v
 return {k:v for k,v in z.items() if v}
def mul(x,y):
 z={}
 for m,v in x.items():
  for n,w in y.items():
   d=dict(m)
   for k,e in n:d[k]=d.get(k,0)+e
   q=tuple(sorted(d.items()));z[q]=z.get(q,0)+v*w
 return {k:v for k,v in z.items() if v}
def atom(k):return {((k,1),):1}
def poly(t):
 if t==aa:return atom('A')
 if t[0]=='num':return {():t[1]} if t[1] else {}
 if t[0]=='var':return atom('v'+str(t[1]))
 if t[0]=='port':return atom('port_'+t[1])
 x,y=poly(t[1]),poly(t[2]);return mul(x,y) if t[0]=='mul' else add(x,y,1 if t[0]=='add' else -1)
# Treat A, v1 and ports as independent; impose only F=v15-(A+1)^3.
one={():1};A=atom('A');Q=atom('v15');F=add(Q,mul(mul(add(A,one),add(A,one)),add(A,one)),-1)
def reduce(P):
 result={};quotient={};queue=list(P.items())
 while queue:
  m,c=queue.pop();d=dict(m);e=d.get('A',0)
  if e<3:result[m]=result.get(m,0)+c;continue
  d['A']=e-3
  if not d['A']:del d['A']
  base=tuple(sorted(d.items()));quotient[base]=quotient.get(base,0)-c
  for var,exp,coef in [('v15',1,1),('A',2,-3),('A',1,-3),('',0,-1)]:
   n=dict(base)
   if var:n[var]=n.get(var,0)+exp
   queue.append((tuple(sorted(n.items())),c*coef))
 result={k:v for k,v in result.items() if v};quotient={k:v for k,v in quotient.items() if v}
 assert add(result,mul(F,quotient))==P
 return result
def degree(P):return max((sum(e for k,e in m if not k.startswith('port_')) for m in P),default=0)
out=[]
for i,row in enumerate(s['residuals']):
 e=row['expr']
 if e[0]!='sub' or e[1][0]!='var' or e[1][1] in (0,15):continue
 k=e[1][1];assert subst(e[2],k,['num',-1])==e[2]
 ds=[]
 for j,r in enumerate(s['residuals']):
  if i==j:continue
  p=poly(subst(r['expr'],k,e[2]));p=p if r['gate']=='q3' else reduce(p);ds.append((r['gate'],degree(p)))
 m=max(d for _,d in ds);out.append({'gate':row['gate'],'kind':row['kind'],'coordinate':k,'maximum_remainder_degree':m,'rows_at_maximum':[g for g,d in ds if d==m]})
assert len(out)==10 and all(x['maximum_remainder_degree']>3 for x in out)
print(json.dumps({'status':'PASS_RESTRICTED_Q3_REMAINDER_SURVEY','source_sha256':hashlib.sha256(raw).hexdigest(),'cases':out,'scope':'single displayed variable-minus-RHS cuts except q3; direct literal substitution followed by exact monic A³->Q-3A²-3A-1 remainder in Z[A,Q,other independent coordinates and ports]; A and v1 treated independently; ports weight 0, other atoms weight 1; no semantic lower bound'},indent=2,sort_keys=True))
