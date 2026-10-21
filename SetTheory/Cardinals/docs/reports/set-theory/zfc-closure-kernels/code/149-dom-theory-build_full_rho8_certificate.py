#!/usr/bin/env python3
"""Append an explicit K/S/Peirce deduction of unrestricted rho8.

The abstraction construction is not trusted by the checker: it emits only
forward schema substitutions and modus-ponens nodes in the final DAG.
"""
import json
from pathlib import Path
import build_classical_certificate as b

# A proof tree may temporarily have assumptions.  Their complete elimination
# is checked before emitting any tree as an unconditional theorem.
class Tree:
 def __init__(self,t,kind,*args):self.t=t;self.kind=kind;self.args=args
 def assumptions(self):
  if self.kind=='hyp':return {self.t}
  if self.kind=='proved':return set()
  return self.args[0].assumptions()|self.args[1].assumptions()
def H(t):return Tree(t,'hyp')
def Theorem(i):return Tree(b.terms[i],'proved',i)
def instance(name,t):return Theorem(b.inst(b.roots[name],t,'unrestricted_rho8:'+name))
def MP(mi,ma):
 assert ma.t[0]==mi.t
 return Tree(ma.t[1],'mp',mi,ma)
def abstract(h,t):
 if t.t==h:return instance('I',b.I(h,h))
 if h not in t.assumptions():
  return MP(t,instance('K',b.I(t.t,b.I(h,t.t))))
 assert t.kind=='mp'
 mi,ma=t.args;a=mi.t;z=t.t
 sma=abstract(h,ma);smi=abstract(h,mi)
 sc=instance('S',b.I(b.I(h,b.I(a,z)),b.I(b.I(h,a),b.I(h,z))))
 return MP(smi,MP(sma,sc))

A,B,C,U=0,1,2,3
F=b.I(b.I(C,U),A);G=b.I(A,C);CU=b.I(C,U)
# Under F and G, the assumption C->U gives A, then C.
p=MP(MP(H(CU),H(F)),H(G))
p=abstract(CU,p)  # ((C->U)->C)
peirce=instance('P',b.I(b.I(b.I(C,U),C),C))
p=MP(p,peirce)
for h in [B,G,F]:p=abstract(h,p)
assert not p.assumptions()
want=b.I(F,b.I(G,b.I(B,C)));assert p.t==want
memo={}
def emit(t):
 if id(t) in memo:return memo[id(t)]
 if t.kind=='proved':return t.args[0]
 assert t.kind=='mp'
 mi,ma=t.args;out=b.mp(emit(mi),emit(ma),'unrestricted_rho8:MP')
 memo[id(t)]=out;return out
b.roots['rho8']=emit(p)

term_table=[];term_ids={}
def intern(t):
 t=b.norm(t)
 if t in term_ids:return term_ids[t]
 entry=[intern(t[0]),intern(t[1])] if isinstance(t,tuple) else {'var':t} if isinstance(t,int) else 'T'
 i=len(term_table);term_ids[t]=i;term_table.append(entry);return i
nodes=[]
for node in b.c.new:
 nn=dict(node);nn['term']=intern(node['term']);rr=dict(nn['rule'])
 for field in ['substitution','major_substitution','minor_substitution']:
  if field in rr:rr[field]={k:intern(v)for k,v in rr[field].items()}
 nn['rule']=rr;nodes.append(nn)
result=dict(b.result);result['nodes']=nodes;result['term_table']=term_table
result['roots']=b.roots;result['theorem']='Unrestricted_rho8_from_dominated_rho8'
result['claim']='For every natural A,B,C,U, restricted rho8 instances with fourth argument <= first argument, truth0, and MP derive unrestricted rho8(A,B,C,U).'
out=(Path(__file__).resolve().parent/'dominated_rho8_full_certificate.json')
out.write_text(json.dumps(result,separators=(',',':'))+'\n')
print(json.dumps({'full_rho8_root':b.roots['rho8'],'nodes':len(nodes),'terms':len(term_table),'bytes':out.stat().st_size},indent=2))
