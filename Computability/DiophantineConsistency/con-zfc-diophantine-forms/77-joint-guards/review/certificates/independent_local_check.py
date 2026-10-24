#!/usr/bin/env python3
"""Independent sparse-ring/AST audit. Does not import the authored builder."""
from pathlib import Path
from itertools import product
from math import isqrt
import hashlib,json,sys
ROOT=Path(__file__).resolve().parents[2]/'certificates'
OUT=Path(__file__).resolve().parent

def need(ok,msg):
 if not ok:raise ValueError(msg)

def padd(a,b,scale=1):
 r=dict(a)
 for m,c in b.items():
  r[m]=r.get(m,0)+scale*c
  if not r[m]:del r[m]
 return r

def pmul(a,b):
 r={}
 for m,c in a.items():
  for n,d in b.items():
   v=tuple(x+y for x,y in zip(m,n));r[v]=r.get(v,0)+c*d
 return {m:c for m,c in r.items() if c}

def parse(ast,names):
 z=(0,)*len(names)
 if isinstance(ast,int):return {z:ast} if ast else {}
 if isinstance(ast,str):
  need(ast in names,'declared AST symbol '+ast)
  k=list(z);k[names.index(ast)]=1;return {tuple(k):1}
 need(type(ast)==list and len(ast)==3 and ast[0] in ('+','-','*'),'valid binary grammar')
 a,b=parse(ast[1],names),parse(ast[2],names)
 return pmul(a,b) if ast[0]=='*' else padd(a,b,-1 if ast[0]=='-' else 1)

def counts(ast):
 nodes=set()
 def visit(x):
  if not isinstance(x,list):return 0
  nodes.add(json.dumps(x,separators=(',',':')))
  return 1+visit(x[1])+visit(x[2])
 tree=visit(ast);return tree,len(nodes)

def evaluate(ast,assignment):
 if isinstance(ast,int):return ast
 if isinstance(ast,str):return assignment[ast]
 a,b=evaluate(ast[1],assignment),evaluate(ast[2],assignment)
 return a+b if ast[0]=='+' else a-b if ast[0]=='-' else a*b

def pair(a,b):return b*b+a if a<b else a*a+a+b

def unpair(z):
 m=isqrt(z);r=z-m*m
 return (r,m) if r<m else (m,r-m)

# Independently composed ordinary-polynomial expressions, not builder imports.
# Python's integers implement Z-polynomial subtraction, never Nat truncated subtraction.
def pairP(z,a,b,t,s):return t*(t-1)+(a-b-s+t*(2*s+1))**2+(4*(z-a-b)-(a+b+s)**2+t)**2

def sextic(z,a,b,s):
 t=(a+b+s)**2-4*(z-a-b)
 return t*(t-1)+(a-b-s+t*(2*s+1))**2

def pred(n,p):return (n-p-1)**2*(n*n+p*p)

def cond(n,a,b,c,s):return (n*(c-b))**2+((c-a)*(n-s-1))**2

def expected(name,a):
 if name in ('max_square_pair_quartic','unpair_left_quartic','unpair_right_quartic'):return pairP(a['z'],a['a'],a['b'],a['t'],a['s'])
 if name=='max_square_pair_sos_quartic':return pairP(a['z'],a['a'],a['b'],a['t'],a['s'])-a['t']*(a['t']-1)+(a['t']*(a['t']-1))**2
 if name=='max_square_pair_sextic':return sextic(a['z'],a['a'],a['b'],a['s'])
 if name=='predecessor_quartic':return pred(a['n'],a['p'])
 if name in ('tree_left_quartic','tree_right_quartic'):return pairP(a['p'],a['a'],a['b'],a['t'],a['s'])+pred(a['n'],a['p'])
 if name=='if_zero_quartic':return cond(a['n'],a['a'],a['b'],a['c'],a['s'])
 if name=='zero_test_quartic':return cond(a['n'],1,0,a['bit'],a['s'])
 if name=='list_head_quartic':return pairP(a['p'],a['a'],a['b'],a['t'],a['s'])+(a['n']-a['p']-1)**2*(a['n']**2+a['p']**2+a['c']**2)+(a['n']*(a['c']-a['a']-1))**2
 raise ValueError(name)

def main():
 reports=[];checks=0
 for path in sorted(ROOT.glob('*quartic.json'))+sorted(ROOT.glob('*sextic.json')):
  d=json.loads(path.read_text());names=d['inputs']+d['auxiliaries'];need(len(names)==len(set(names)),path.name+' distinct coordinates')
  p=parse(d['expression'],names);degree=max(sum(m) for m in p)
  tree,dag=counts(d['expression'])
  literal={tuple(t['powers']):int(t['coefficient']) for t in d['expanded_terms']}
  need(p==literal,path.name+' full exact sparse expansion')
  need(degree==d['degree'] and len(p)==d['monomials'],path.name+' dimensions/degree')
  need((tree,dag)==(d['tree_binary_operations'],d['shared_dag_binary_operations']),path.name+' exact operation counts')
  need(len(d['auxiliaries'])==d['auxiliary_count'] and len(names)==d['total_variables'],path.name+' quantified dimensions')
  need(all(any(m[j] for m in p) for j in range(len(names))),path.name+' liveness')
  for tup in product(range(3),repeat=len(names)):
   v=dict(zip(names,tup));value=evaluate(d['expression'],v)
   need(value==expected(d['name'],v),path.name+' independently written formula agreement')
   need(value>=0,path.name+' diagnostic nonnegativity');checks+=1
  reports.append({'name':d['name'],'degree':degree,'auxiliaries':d['auxiliary_count'],'tree_operations':tree,'shared_dag_operations':dag,'full_expansion':True,'sha256':hashlib.sha256(path.read_bytes()).hexdigest()})
 # Diagnostic soundness deliberately includes non-Boolean selectors.
 for a,b,z,t,s in product(range(5),range(5),range(65),range(4),range(8)):
  value=pairP(z,a,b,t,s)
  need(value>=0 and (value!=0 or z==pair(a,b)),'quartic pair diagnostic');checks+=1
 for a,b,z,s in product(range(5),range(5),range(65),range(8)):
  value=sextic(z,a,b,s)
  need(value>=0 and (value!=0 or z==pair(a,b)),'sextic pair diagnostic');checks+=1
 for n,p in product(range(50),repeat=2):
  need((pred(n,p)==0)==(p==max(n-1,0)),'predecessor diagnostic');checks+=1
 for n,a,b,c,s in product(range(6),repeat=5):
  value=cond(n,a,b,c,s)
  need(value>=0 and (value!=0 or c==(a if n==0 else b)),'conditional diagnostic');checks+=1
 for z in range(10000):
  a,b=unpair(z);t=int(a<b);s=b-a-1 if t else a-b
  need(pair(a,b)==z and pairP(z,a,b,t,s)==0 and sextic(z,a,b,s)==0,'pair/unpair explicit completeness');checks+=1
 for n in range(300):
  p=max(n-1,0);a,b=unpair(p);t=int(a<b);s=b-a-1 if t else a-b;c=0 if n==0 else a+1
  v={'n':n,'p':p,'a':a,'b':b,'t':t,'s':s,'c':c}
  need(expected('list_head_quartic',v)==0,'list head including nil completeness');checks+=1
 # Guards against two tempting but invalid domain/shape modifications.
 need((-1)*(-2)>0,'integer selector nonnegativity')
 need(cond(0,1,0,9,-1)==0,'negative slack destroys conditional soundness: explicit negative control')
 # Missing c^2 would allow false nonzero nil heads because n multiplier vanishes.
 need(pairP(0,0,0,0,0)+pred(0,0)+(0*(7-0-1))**2==0,'missing nil constraint negative control')
 result={'status':'PASS','optimized_mode':not __debug__,'polynomials':reports,'diagnostic_assignments':checks,'negative_controls':['Allowing negative conditional slack s=-1 admits arbitrary c at n=0.','Deleting c^2 from list-head predecessor norm admits c=7 at nil.'],'scope':'Independent literal AST/operation counts and exact sparse expansions plus diagnostics; universal semantic proof is a separately reviewed mathematical argument, not finite enumeration.'}
 target='LOCAL_CHECKS_OPTIMIZED.json' if not __debug__ else 'LOCAL_CHECKS.json';(OUT/target).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
