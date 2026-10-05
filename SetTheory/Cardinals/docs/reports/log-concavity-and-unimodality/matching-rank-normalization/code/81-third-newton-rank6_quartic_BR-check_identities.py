"""Exact construction checks for the BR reduction, separate from cone expansion."""
from build_br import *
from collections import Counter
from itertools import combinations
N={i:xs[i-1] for i in range(1,8)}
nv=sum(N[i] for i in N if i&1);mv=[sum(N[i] for i in N if i&(1<<j)) for j in range(3)]

def need(c,m):
 if not c:raise RuntimeError(m)
def same(a,b,msg):need(s.expand(a-b)==0,msg)
def canon(U,C):
 order=[i for i in range(3) if U>>i&1]+[i for i in range(3) if not U>>i&1]
 perm=[order.index(i) for i in range(3)];v=image(C,perm);u=(1<<U.bit_count())-1
 if u==1:v&=6
 elif u==3:v=(1 if v&3 else 0)+(4 if v&4 else 0)
 elif v.bit_count()>=2:v=3
 return u,v
collapse=0
for U in range(1,8):
 for C in range(8):
  u,c=canon(U,C);need(cnt((U,C))==cnt((u,c)),'h collapse');collapse+=1
  for D in range(8):
   _,d=canon(U,D)
   need(cnt((U,C,D))==cnt((u,c,d)),'chi collapse')
   need(cnt((U,C|D))==cnt((u,c|d)),'union collapse');collapse+=2

def choose(x,j):
 v=s.Integer(1)
 for a in range(j):v*=x-a
 return v/s.factorial(j)
P={i:0 for i in range(1,8)}
for S,T in combinations_with_replacement(range(1,8),2):
 profile=0
 for miss in range(3):
  i,j=[c for c in range(3) if c!=miss]
  if (S>>i&1 and T>>j&1) or (S>>j&1 and T>>i&1):profile|=1<<miss
 if profile:P[profile]+=choose(N[S],2) if S==T else N[S]*N[T]
qL=sum(s.prod(choose(N[x],b.count(x)) for x in set(b)) for b in BASES)
checks=0
for U,J,C1,C2 in profiles():
 core=(J,C1,C2);rt,E,rr,iv,det=rdata(U,J)
 same(E.subs(n,nv),endpoint(core,(('B',0),('R',U))),'E');checks+=1
 D=sum(cnt((U,core[(i+1)%3],core[(i+2)%3]))<<i for i in range(3))
 qbr=U.bit_count()*qL
 for T in range(1,8):
  union=0
  for i in range(3):
   if T>>i&1:union|=core[i]
  qbr+=P[T]*cnt((U,union))
 qbr+=sum(N[S] for S in range(1,8) if S&D)
 same(qbr,endpoint(core,(('B',0),('B',1),('B',2),('R',U))),'qBR');checks+=1
 for idx,C in enumerate((C1,C2),1):
  t=sum(N[S] for S in N if S&1 and S>>idx&1);p=nv*mv[idx]-t*(t+1)/2
  for S in rt:
   value=p*cnt((U,S))+nv*cnt((C,U,S))+mv[idx]*cnt((J,U,S))-t*(cnt((J,U,S))+cnt((C,U,S))-cnt((J|C,U,S)))
   same(value,endpoint(core,(('B',0),('B',idx),('R',U),('R',S))),'BR cross');checks+=1
 for S,T in combinations_with_replacement(rt,2):
  same(nv*cnt((U,S,T)),endpoint(core,(('B',0),('R',U),('R',S),('R',T))),'RR block');checks+=1
out={'all_pass':True,'collapse_identities':collapse,'endpoint_polynomial_identities':checks,'core_profiles':len(profiles())}
(ROOT/'identity_checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
