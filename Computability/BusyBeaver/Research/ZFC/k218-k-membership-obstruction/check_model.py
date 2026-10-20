#!/usr/bin/env python3
"""Independent finite native-constructor model certificate. No search code imported."""
from pathlib import Path
from itertools import product
import hashlib,json,math
P=Path(__file__).resolve().parent
m=json.loads((P/'search3-d1.json').read_text());n=m['n'];D=set(range(n-m['nd'],n));f=m['F'];t=m['T']
assert (n,D,f,t)==(3,{2},0,2)
# Native constructor ASTs preserve every binder label and repeated quantifier.
def I(a,b):return ('I',a,b)
def R(a,b):return ('R',a,b)
def E(a,b):return ('E',a,b)
def Q(a,b):return ('Q',a,b)
def N(a):return I(a,'f')
def Ex(i,a):return N(Q(i,N(a)))
def req(b,k,x):return Q(b,I(x,N(Q(b,I(x,N(R(b,k)))))))
def clos(a,b,k,x):return Q(b,I(R(b,k),N(Q(a,I(x,N(Q(a,I(Q(k,I(R(k,a),R(k,b))),req(b,k,x)))))))))
def nks(a,b,c):return Q(c,I(clos(a,b,c,c),N(req(b,c,c))))
def bundle(a,b,c):return N(I(I(R(a,b),Q(c,R(a,b))),nks(a,b,c)))
def L(a,b,c,u):return I(I(I(c,u),a),I(I(a,c),I(b,c)))
rows={
 'rho1':(Ex('a',E('a','b')),'ab'),
 'rho2':(I(Q('a',I('b','c')),I(Q('a','b'),Q('a','c'))),'abc'),
 'rho3':(I(E('a','b'),I(R('c','a'),R('c','b'))),'abc'),
 'rho4':(I(Q('a',Q('b','c')),Q('b',Q('a','c'))),'abc'),
 'rho5':(I(E('c','a'),I(R('c','b'),R('a','b'))),'abc'),
 'rho6':(I(Ex('a',Q('a','b')),'b'),'ab'),
 'G':(I(E('c','a'),I(E('c','b'),Q(R('a','b'),E('a','b')))),'abc'),
 'bundle222':(bundle('a','b','c'),'abc'),
 'K':(I('a',I('b','a')),'ab'),
 'restricted_rho8_RAB':(L('a','b','c',R('a','b')),'abc'),
 'truth_transport':(I(I('t','c'),I('b','c')),'bc'),
 'quantified_DNE':(I(N(N(Q('a','b'))),Q('a','b')),'ab')}
def ev(x,env):
 if isinstance(x,str):return env[x]
 return m[x[0]][n*ev(x[1],env)+ev(x[2],env)]
checks={}
for name,(tree,vars) in rows.items():
 outputs=[]
 for vals in product(range(n),repeat=len(vars)):
  env=dict(zip(vars,vals),f=f,t=t);outputs.append(ev(tree,env))
 assert set(outputs)<=D,(name,outputs)
 checks[name]={'cases':len(outputs),'outputs':sorted(set(outputs))}
assert m['I'][n*t+t]==t and m['R'][n*t+t]==f and t in D and f not in D
assert all(not(a in D and m['I'][n*a+b] in D) or b in D for a,b in product(range(n),repeat=2))
assert all(m['Q'][n*a+b] in D for a in range(n) for b in D)
# Native total-code recursion and concrete reachable witnesses.
def pair(a,b):return (a+b)*(a+b+1)//2+b
def unpair(x):
 s=(math.isqrt(8*x+1)-1)//2;b=x-s*(s+1)//2;return s-b,b
def code(op,a,b):return 4*pair(a,b)+'IREQ'.index(op) if False else 4*pair(a,b)+{'I':0,'R':1,'Q':2,'E':3}[op]
values=[t]
for k in range(1,20001):
 a,b=unpair(k//4);assert a<k and b<k
 op=('I','R','Q','E')[k%4];values.append(m[op][n*values[a]+values[b]])
witness={0:1,1:16,2:0};assert all(values[k]==v for v,k in witness.items())
for a,b in product(range(32),repeat=2):
 for op in ('I','R','Q','E'):
  k=code(op,a,b)
  assert values[k]==m[op][n*values[a]+values[b]]
# Exact failures show why this is stronger than a heuristic no-proof result.
other={
 'identity':(I('a','a'),'a'),
 'EFQ':(I('f','a'),'a'),
 'composition_B':(I(I('b','c'),I(I('a','b'),I('a','c'))),'abc'),
 'S':(I(I('a',I('b','c')),I(I('a','b'),I('a','c'))),'abc'),
 'all_formula_DNE':(I(N(N('a')),'a'),'a'),
 'unrestricted_rho8':(L('a','b','c','u'),'abcu')}
failures={}
for name,(tree,vars) in other.items():
 bad=[]
 for vals in product(range(n),repeat=len(vars)):
  env=dict(zip(vars,vals),f=f,t=t);v=ev(tree,env)
  if v not in D:bad.append({'values':dict(zip(vars,vals)),'natural_parameters':{x:witness[y] for x,y in zip(vars,vals)},'output':v})
 assert bad,name
 failures[name]={'failure_count':len(bad),'first':bad[0]}
# Check every other membership orientation and the cheap fixed variants too.
variants={x+y:R(x,y) for x in 'abc' for y in 'abc' if x!=y}
variants.update(A='a',B='b',C='c',truth='t',F='f')
variant_results={}
for label,u in variants.items():
 bad=[]
 for vals in product(range(n),repeat=3):
  env=dict(zip('abc',vals),f=f,t=t);v=ev(L('a','b','c',u),env)
  if v not in D:bad.append({'values':dict(zip('abc',vals)),'output':v})
 variant_results[label]={'valid':not bad,'failures':bad}
result={'status':'EXACT_CODE_DEPENDENT_K_RAB_MATRIX_PASS','model':m,'rows':checks,'truth_alias':True,'native_falsum_binding':True,'MP':True,'GEN':True,'carrier_value_witnesses':witness,'finite_code_regressions':{'initial_codes':20001,'constructor_pairs':1024},'failures':failures,'other_fourth_variants':variant_results,'scope':'Finite algebra supports an all-natural course-of-values code valuation and derivation induction. In particular K+RAB+rho1-6+G+entire gated bundle is consistent, even with every quantified-DNE row. Gates are not discarded in the calculus: checking all value triples is a sufficient superset for soundness. No ordinary assignment semantics, arbitrary substitution rule, or proof-assistant run is used.'}
(P/'model-check.json').write_text(json.dumps(result,indent=2)+'\n');(P/'literal-rows.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps({'status':result['status'],'rows':checks,'failures':failures,'other_fourth_variants':{k:len(v['failures']) for k,v in variant_results.items()}},indent=2))
