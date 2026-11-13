#!/usr/bin/env python3
"""Exact local ring certificate from pinned sign14 AST to named residuals.

Intermediate aliases are introduced only after their defining polynomial
identity has been checked. Q=B+1 is the sole non-definitional rewrite.
"""
import collections,hashlib,json
from pathlib import Path
PTH=Path(__file__).resolve().parent;src=PTH.parent/'nine-sharing-sign14-tau-candidate/seed.json';raw=src.read_bytes();assert hashlib.sha256(raw).hexdigest()=='7048a10d409ab5ff8031a444cd32117ba772b3834425c17a066188338e189ea9';seed=json.loads(raw)
class P:
 def __init__(self,d):self.d={m:c for m,c in d.items() if c}
 def __add__(self,o):
  o=as_p(o);d=self.d.copy()
  for m,c in o.d.items():d[m]=d.get(m,0)+c
  return P(d)
 def __radd__(self,o):return self+o
 def __neg__(self):return P({m:-c for m,c in self.d.items()})
 def __sub__(self,o):return self+-as_p(o)
 def __rsub__(self,o):return as_p(o)+-self
 def __mul__(self,o):
  o=as_p(o);d={}
  for a,x in self.d.items():
   for b,y in o.d.items():
    m=tuple(sorted(a+b));d[m]=d.get(m,0)+x*y
  return P(d)
 def __rmul__(self,o):return self*o
 def __pow__(self,n):
  r=as_p(1)
  for _ in range(n):r=r*self
  return r
 def subst(self,mapping):
  out=as_p(0)
  for m,c in self.d.items():
   term=as_p(c)
   for name in m:term=term*mapping.get(name,S(name))
   out=out+term
  return out
 def __eq__(self,o):return self.d==as_p(o).d
 def __repr__(self):return repr(self.d)
def as_p(x):return x if isinstance(x,P) else P({():x})
def S(name):return P({(name,):1})
names=['judge','bound','slack','divisor','factor','index','clock','height','width','count','left','right','target','extra']
v={i+1:S(name) for i,name in enumerate(names)};J,F,A,Z,f,I,T,h,w,n,u,vv,y,g=[v[i] for i in range(1,15)]
B,Q,X,Y,E,C,AA,H,DELTA,D,R,V,TAU,ELL,SCALE,M,KY,L=[S(x) for x in ['BASE','UNIT','HORIZONTAL','VERTICAL','PRODUCT','CENTER','SUM','WEIGHT','DELTA','ROOT','RANK','INNER','CARRY','LENGTH','SCALE','M','GAP_VERTICAL','MASK_LINEAR']]
K,MU,OMEGA,BETA=[S(x) for x in ['K','MU','OMEGA','BETA']]
counts=collections.Counter();sizes={}
def intern(t):
 x=tuple(t) if len(t)==2 else (t[0],intern(t[1]),intern(t[2]));counts[x]+=1;sizes[x]=1 if len(x)==2 else 1+sizes[x[1]]+sizes[x[2]];return x
roots=[intern(row['expr']) for row in seed['residuals']];shared=sorted((x for x in counts if counts[x]>=2 and sizes[x]>=9),key=lambda x:(sizes[x],repr(x)));assert len(shared)==44
# Cut only syntactically exact occurrences of the shifted coordinate, base and unit.
pos={('add',('var',i),('num',1)):v[i] for i in range(1,15)}
b_tree=('mul',('port','beta'),('add',('var',1),('num',1)));q_tree=('add',b_tree,('num',1));cuts={**pos,b_tree:B,q_tree:Q}
ports={'beta':BETA,'K0':K,'MC':MU,'MF':OMEGA}
def resolve(t,skip=None):
 if t!=skip and t in cuts:return cuts[t]
 op=t[0]
 if op=='num':return as_p(t[1])
 if op=='port':return ports[t[1]]
 if op=='var':return as_p(1) if t[1]==0 else v[t[1]]-1
 a=resolve(t[1]);b=resolve(t[2]);return {'add':lambda:a+b,'sub':lambda:a-b,'mul':lambda:a*b}[op]()
# These substitutions are applied only after their defining identities have
# been checked. They keep each ring calculation small and fully exact.
def normalize(x):
 return x.subst({'ROOT':X+AA*C+g*H,'RANK':M*(Q**2-1)+L*J}).subst({'M':B*(Q-F)+A,'HORIZONTAL':w*Q}).subst({'BASE':Q-1})
def assert_equal(label,a,b):
 x=normalize(a);y=normalize(b)
 if x!=y:raise AssertionError((label,x,y))
verified=[]
def bind(i,expected,replacement):
 actual=resolve(shared[i],shared[i]);assert_equal(f'shared{i:02}',actual,expected);cuts[shared[i]]=replacement;verified.append(i)
bind(4,MU+Q*OMEGA,L)
bind(5,w*Q,X)
bind(7,X-1,X-1)
bind(13,h*(Q**3),Y)
bind(14,B*(Q-F)+A,M)
bind(16,(u+vv)*Y,KY)
bind(17,KY+u,C)
bind(18,X*Y,E)
bind(22,M*(Q**2),M*(Q**2))
bind(23,E+Y,AA)
bind(26,4*AA+3,H)
bind(27,R+M,R+M)
bind(29,E*KY,ELL)
bind(36,E*n+u+vv-R,TAU)
bind(37,(f**2)*(C*T-R)-C,V)
bind(38,D-1,D-1)
bind(40,(AA**2)+H,DELTA)
bind(41,(D**2)-1,(D**2)-1)
bind(42,I*((D**2)-1),SCALE)
bind(43,SCALE**2,SCALE**2)
expected=[(D**2)-DELTA*(C**2)-1,TAU**2-ELL*(ELL+u+vv)-1,(K+w)*(Q-F-A)+(Q-F)-Z*B-1,y**2-(SCALE**2)*(y**2-V**2)-1,DELTA*(f**2)-(SCALE**2)-DELTA]
for i,(r,e) in enumerate(zip(roots,expected)):assert_equal(f'row{i:02}',resolve(r,r),e)
# Explicitly record the named abbreviations used in the presentation and in the
# validated cuts; substituting these reconstructs each fully defined formula.
named={'BASE':BETA*J,'UNIT':B+1,'HORIZONTAL':w*Q,'VERTICAL':h*(Q**3),'PRODUCT':X*Y,'GAP_VERTICAL':(u+vv)*Y,'CENTER':KY+u,'SUM':E+Y,'WEIGHT':4*AA+3,'DELTA':AA**2+H,'ROOT':X+AA*C+g*H,'M':B*(Q-F)+A,'MASK_LINEAR':MU+Q*OMEGA,'RANK':M*(Q**2-1)+L*J,'CARRY':E*n+u+vv-R,'INNER':(f**2)*(C*T-R)-C,'SCALE':I*(D**2-1),'LENGTH':E*KY}
assert len(named)==18 and len(verified)==20
print(json.dumps({'status':'PASS_EXACT_LOCAL_RING_CERTIFICATE','seed_sha256':hashlib.sha256(raw).hexdigest(),'validated_shared_nodes':verified,'residuals':5,'scope':'Exact ring identities after syntactic AST cuts; external checker, not Lean proof.'},sort_keys=True))
