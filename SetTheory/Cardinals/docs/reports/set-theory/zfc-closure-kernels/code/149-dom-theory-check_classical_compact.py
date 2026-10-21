#!/usr/bin/env python3
"""Check a finite dominated-rho8 proof; Python standard library only.

No unification, external prover, Coq installation, or search is used.
A compact shared term table is decoded into an independently interned algebra.
The sole arithmetic-code normalization is I(T,T)=T, where T means code 0.
"""
import json,sys
from collections import Counter
from pathlib import Path

class Terms:
 def __init__(self):
  self.items=[];self.index={};self.vars=[];self.T=self.put(('T',))
 def put(self,key):
  if key in self.index:return self.index[key]
  i=len(self.items);self.items.append(key);self.index[key]=i
  self.vars.append(frozenset([key[1]]) if key[0]=='v' else
                   self.vars[key[1]]|self.vars[key[2]] if key[0]=='I' else frozenset())
  return i
 def var(self,n):return self.put(('v',n))
 def imp(self,a,b):return self.T if a==b==self.T else self.put(('I',a,b))
 def parts(self,t):
  if t==self.T:return self.T,self.T
  kind,*args=self.items[t];assert kind=='I',('not an implication',t)
  return tuple(args)
 def subst(self,t,env):
  assert self.vars[t]<=set(env),('missing variable substitution',self.vars[t]-set(env))
  memo={}
  def go(x):
   if x in memo:return memo[x]
   kind,*args=self.items[x]
   ans=env[args[0]] if kind=='v' else self.imp(go(args[0]),go(args[1])) if kind=='I' else self.T
   memo[x]=ans;return ans
  return go(t)
 def canonical(self,t):
  names={};memo={}
  def go(x):
   if x in memo:return memo[x]
   kind,*args=self.items[x]
   if kind=='v':
    if args[0] not in names:names[args[0]]=len(names)
    ans=self.var(names[args[0]])
   elif kind=='I':ans=self.imp(go(args[0]),go(args[1]))
   else:ans=self.T
   memo[x]=ans;return ans
  return go(t)
 def subterm_depth(self,a,u):
  memo={}
  def go(x):
   if x==u:return 0
   if x in memo:return memo[x]
   kind,*args=self.items[x]
   ans=1+min(go(args[0]),go(args[1])) if kind=='I' else 10**9
   memo[x]=ans;return ans
  return go(a)

def check(path):
 data=json.loads(Path(path).read_text());assert data['format']=='term_dag_v1'
 algebra=Terms();mapping=[]
 for k,t in enumerate(data['term_table']):
  if t=='T':x=algebra.T
  elif isinstance(t,dict):
   assert set(t)=={'var'} and type(t['var'])==int and t['var']>=0
   x=algebra.var(t['var'])
  else:
   assert isinstance(t,list) and len(t)==2
   assert all(type(y)==int and 0<=y<k for y in t),('term topology',k)
   x=algebra.imp(mapping[t[0]],mapping[t[1]])
  mapping.append(x)
 def ref(j):
  assert type(j)==int and 0<=j<len(mapping),('bad term reference',j)
  return mapping[j]
 def env(e):
  assert isinstance(e,dict)
  assert all(k.isdigit() and str(int(k))==k for k in e), 'bad variable name'
  return {int(k):ref(v)for k,v in e.items()}
 proof=[];counts=Counter();maxdepth=0
 for k,node in enumerate(data['nodes']):
  assert node['id']==k,('node id',k)
  t=ref(node['term']);r=node['rule'];kind=r['kind'];counts[kind]+=1
  if kind=='truth':assert t==algebra.T,('truth',k)
  elif kind=='dominated_rho8':
   pre,post=algebra.parts(t);cu,a=algebra.parts(pre);c,u=algebra.parts(cu)
   ac,bc=algebra.parts(post);a2,c2=algebra.parts(ac);b,c3=algebra.parts(bc)
   assert a==a2 and c==c2==c3,('rho8 shape',k)
   if u!=algebra.T:
    depth=algebra.subterm_depth(a,u)
    assert depth<10**9,('U is not a subterm of A',k)
    maxdepth=max(maxdepth,depth)
  elif kind=='substitution':
   p=r['parent'];assert type(p)==int and 0<=p<k,('parent topology',k)
   assert algebra.subst(proof[p],env(r['substitution']))==t,('substitution',k)
  elif kind in {'mp','mp_substitution'}:
   ma,mi=r['major'],r['minor']
   assert all(type(j)==int and 0<=j<k for j in [ma,mi]),('MP topology',k)
   major,minor=proof[ma],proof[mi]
   if kind=='mp_substitution':
    major=algebra.subst(major,env(r['major_substitution']))
    minor=algebra.subst(minor,env(r['minor_substitution']))
   antecedent,consequent=algebra.parts(major)
   assert antecedent==minor,('MP antecedent',k)
   assert (algebra.canonical(consequent)==algebra.canonical(t) if kind=='mp_substitution' else consequent==t),('MP consequent',k)
  else:raise AssertionError(('unsupported proof rule',kind))
  proof.append(t)
 I=algebra.imp;p,q,r=[algebra.var(j)for j in range(3)]
 expected={'I':I(p,p),'K':I(p,I(q,p)),'P':I(I(I(p,q),p),p),
           'cd59':I(I(p,q),I(I(I(p,r),p),q)),
           'B':I(I(p,q),I(I(q,r),I(p,r))),
           'S':I(I(p,I(q,r)),I(I(p,q),I(p,r)))}
 if 'rho8' in data['roots']:
  a,bb,c,u=[algebra.var(j)for j in range(4)]
  expected['rho8']=I(I(I(c,u),a),I(I(a,c),I(bb,c)))
 assert set(data['roots'])==set(expected),'wrong collection of claimed roots'
 for name,t in expected.items():
  root=data['roots'][name];assert type(root)==int and 0<=root<len(proof)
  assert algebra.canonical(proof[root])==algebra.canonical(t),('wrong root theorem',name)
 return {'verified':True,'proof_nodes':len(proof),'shared_terms':len(mapping),
         'rules':dict(counts),'roots':data['roots'],'maximum_subterm_depth':maxdepth,
         'normalization':'I(0,0)=0 only','trust':'forward substitutions, direct MP, and structural axiom checks'}

if __name__=='__main__':
 print(json.dumps(check(sys.argv[1] if len(sys.argv)>1 else Path(__file__).with_name('classical_basis_certificate_compact.json')),indent=2))
