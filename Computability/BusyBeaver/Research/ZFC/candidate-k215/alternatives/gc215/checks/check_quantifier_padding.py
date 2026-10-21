#!/usr/bin/env python3
"""Read an explicit finite proof as data. Independent of the proof generator.
All statement variables denote arbitrary natural codes; no wellformedness or
numerical constructor injectivity is assumed. Uses only Python standard library.
"""
import hashlib,json,sys
from collections import Counter
from pathlib import Path

def require(b,msg):
 if not b:raise ValueError(msg)
def imp(a,b):return ('imp',a,b)
def all_(i,a):return ('all',i,a)
F=('const',1)
def neg(a):return imp(a,F)
def rho(i,b):return imp(neg(all_(i,neg(all_(i,b)))),b)
def check(path):
 d=json.loads(path.read_text());require(d['format']=='quantifier_padding_v1','format')
 ts=[]
 for j,x in enumerate(d['terms']):
  tag=x[0]
  if tag=='var':require(len(x)==2 and x[1] in ('i','b'),'variable');t=(tag,x[1])
  elif tag=='const':require(len(x)==2 and type(x[1]) is int and x[1]>=0,'constant');t=tuple(x)
  else:
   require(tag in ('imp','all','succ'),'constructor')
   require(len(x)==(2 if tag=='succ' else 3),'arity')
   require(all(type(k)is int and 0<=k<j for k in x[1:]),'forward term')
   t=(tag,*(ts[k] for k in x[1:]))
  ts.append(t)
 proof=[];used=Counter();restricted=[]
 for n,node in enumerate(d['nodes']):
  require(node['id']==n,'node id');require(0<=node['term']<len(ts),'term reference')
  f=ts[node['term']];r=node['rule'];ps=node['parents'];used[r]+=1
  require(all(type(k)is int and 0<=k<n for k in ps),'forward proof')
  if r=='MP':
   require(len(ps)==2,'MP arity');m,p=(proof[k] for k in ps)
   require(m[0]=='imp' and m[1]==p and m[2]==f,'MP equation')
  elif r=='GEN':
   require(len(ps)==1 and f[0]=='all' and f[2]==proof[ps[0]],'closed GEN')
  else:
   require(not ps,'axiom has premise')
   require(f[0]=='imp','axiom implication')
   if r=='K':
    a=f[1];require(f[2][0]=='imp' and f[2][2]==a,'K instance')
   elif r=='S':
    lhs=f[1];require(lhs[0]=='imp' and lhs[2][0]=='imp','S antecedent')
    a,b,c=lhs[1],lhs[2][1],lhs[2][2]
    require(f==imp(imp(a,imp(b,c)),imp(imp(a,b),imp(a,c))),'S instance')
   elif r=='rho2':
    lhs=f[1];require(lhs[0]=='all' and lhs[2][0]=='imp','rho2 shape')
    i,a,b=lhs[1],lhs[2][1],lhs[2][2]
    require(f==imp(all_(i,imp(a,b)),imp(all_(i,a),all_(i,b))),'rho2 instance')
   elif r=='rho6_strict':
    p=f[2];require(p[0]=='imp' and p[1][0]=='imp','pad shape')
    e=p[1][1];require(e==p[1][2] and e[0]=='succ','positive identity pad')
    i=e[1];b=p[2]
    require(f==rho(i,p),'rho6 exact instance')
    # e=i+1; I(e,e)=8e(e+1); I(W,b)>=4W.
    # 32(i+1)(i+2)-i = 32i^2+95i+64 has positive
    # constant and nonnegative coefficients, for every natural i.
    require((32,95,64)==(32,32*3-1,32*2),'strict bound arithmetic')
    restricted.append(n)
   else:raise ValueError('unknown rule '+r)
  proof.append(f)
 root=d['root'];require(proof[root]==rho(('var','i'),('var','b')),'root equation')
 need=set();todo=[root]
 while todo:
  n=todo.pop()
  if n not in need:need.add(n);todo.extend(d['nodes'][n]['parents'])
 require(len(need)==len(proof),'unneeded proof nodes')
 require(len(restricted)==1,'exactly one strict rho6 premise')
 return {'verdict':'PASS','scope':'All-natural symbolic Hilbert proof; no machine claim.',
  'proof_nodes':len(proof),'term_nodes':len(ts),'rules':dict(used),'restricted_rho6_nodes':restricted,
  'strict_bound_polynomial_coefficients_descending':[32,95,64],
  'certificate_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
  'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
if __name__=='__main__':
 p=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name('quantifier_padding_certificate.json')
 result=check(p)
 print(json.dumps(result,indent=2))
 if len(sys.argv)>2:Path(sys.argv[2]).write_text(json.dumps(result,indent=2)+'\n')
