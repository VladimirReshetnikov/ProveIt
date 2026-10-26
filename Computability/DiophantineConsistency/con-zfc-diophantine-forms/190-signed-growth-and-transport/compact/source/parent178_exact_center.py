"""Sparse exact polynomial-part Pell centers; no symbolic dependencies."""
from collections import defaultdict
from pathlib import Path
import json
names=['A','Y','k','U','b','c'];n=len(names)
def C(x):return {(0,)*n:x} if x else {}
def var(i):m=[0]*n;m[i]=1;return {tuple(m):1}
def add(*ps):
 d=defaultdict(int)
 for p in ps:
  for m,c in p.items():d[m]+=c
 return {m:c for m,c in d.items() if c}
def scale(a,p):return {m:a*c for m,c in p.items() if a*c}
def mul(p,q):
 d=defaultdict(int)
 for a,c in p.items():
  for b,e in q.items():d[tuple(x+y for x,y in zip(a,b))]+=c*e
 return {m:c for m,c in d.items() if c}
def sq(p):return mul(p,p)
def quo(p,j):return {(m[0]-j,)+m[1:]:c for m,c in p.items() if m[0]>=j}
def weighted(p,w):return max(sum(a*b for a,b in zip(m,w)) for m in p)
def top(p,w):
 d=weighted(p,w);return {m:c for m,c in p.items() if sum(a*b for a,b in zip(m,w))==d}
def serial(p):return [[c,list(m)] for m,c in sorted(p.items())]
def show(p):
 return ' + '.join(str(c)+'*'+'*'.join(v+('^'+str(a) if a!=1 else '') for v,a in zip(names,m) if a) for m,c in sorted(p.items()))

A,Y,k,U,b,c=[var(i) for i in range(n)]
e2=mul(sq(k),sq(Y))
e1=mul(mul(sq(k),Y),add(C(1),scale(-2,Y),scale(-2,sq(Y))))
yp=mul(Y,add(Y,C(1)))
e0=add(C(1),mul(sq(k),mul(yp,add(yp,C(-1)))))
E=add(mul(e2,sq(A)),mul(e1,A),e0)
Delta=add(sq(A),C(-1))
f=add(C(1),scale(2,mul(mul(Delta,sq(U)),E)))
V=add(mul(f,b),scale(-1,c));F=mul(E,V)
G=mul(E,add(C(1),mul(mul(Delta,sq(U)),E)))
W1=mul(U,add(scale(2,mul(A,F)),scale(-1,quo(F,1))))
W8=mul(U,add(scale(8,mul(A,F)),scale(-4,quo(F,1)),scale(-1,quo(F,3))))
W16=mul(U,add(scale(16,mul(A,F)),scale(-8,quo(F,1)),scale(-2,quo(F,3)),scale(-1,quo(F,5))))
weights=[4,2,1,7,4,3]
def summaries():
 out={}
 if any(c%2 for c in W8.values()):raise ValueError('W8 is not coefficientwise even')
 W4={m:c//2 for m,c in W8.items()}
 for name,W,scaleG in [('first_order',W1,4),('scale4_second_order',W4,16),('second_order',W8,64),('whole_polynomial_part',W16,256)]:
  D=add(sq(W),scale(-scaleG,mul(G,sq(V))))
  out[name]={'center_terms':len(W),'D_terms':len(D),'center_weighted_degree':weighted(W,weights),'D_weighted_degree':weighted(D,weights),'D_top_terms':serial(top(D,weights)),'D_top_formula':show(top(D,weights)),'D_max_A_degree':max(m[0] for m in D),'center':serial(W),'D':serial(D)}
 return {'variables':names,'weights':weights,'E':serial(E),'F':serial(F),'F_A_coefficients':[serial({(0,)+m[1:]:c for m,c in F.items() if m[0]==j}) for j in range(7)],'results':out}
if __name__=='__main__':
 data=summaries()
 for name,x in data['results'].items():print(name,{k:v for k,v in x.items() if k not in ['center','D','D_top_terms']})
 Path(__file__).with_name('RESULTS.json').write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')

