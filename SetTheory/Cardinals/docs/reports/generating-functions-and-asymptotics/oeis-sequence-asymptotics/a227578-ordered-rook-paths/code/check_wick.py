import json
from collections import Counter
import sympy as s
from pathlib import Path

def pairings(xs):
 if not xs:
  yield [];return
 a=xs[0]
 for i,b in enumerate(xs[1:]):
  rest=xs[1:i+1]+xs[i+2:]
  for p in pairings(rest):yield [(a,b)]+p

def wick_cycles(lengths):
 n=sum(lengths);gam={};j=0
 for m in lengths:
  for i in range(m):gam[j+i]=j+(i+1)%m
  j+=m
 out=Counter()
 for pairs in pairings(list(range(n))):
  pi={a:b for a,b in pairs};pi.update({b:a for a,b in pairs});perm={i:gam[pi[i]] for i in range(n)};seen=set();cy=0
  for i in range(n):
   if i in seen:continue
   cy+=1;j=i
   while j not in seen:seen.add(j);j=perm[j]
  out[cy]+=1
 return dict(sorted(out.items()))
a4=wick_cycles([4]);a33=wick_cycles([3,3]);assert a4=={1:1,3:2};assert a33=={1:3,3:12}
k=s.symbols('k',positive=True,integer=True);mu=(k+1)/k**2;a=(k+1)*(k+2)/k**3;b=(k+1)*(k*k+6*k+6)/k**4;c=(k+1)*(k**3+14*k*k+36*k+24)/k**5;v=a/mu
A=(k-1)*a/(2*k*mu)-(k-1)*mu/2-k/s.Integer(12)-a*a/(2*k*mu**2)+b/(2*k*mu)
B=a**3/(8*k*mu**3)-a*b/(4*k*mu**2)
d=s.factor(A*(k*k-1)/v+B*(k*k-1)*(k*k+1)/v**2+c/(24*mu)*(k*k-1)*(2*k*k-3)/(k*v**2)-b*b/(72*mu**2)*3*(k*k-1)*(k*k-4)/(k*v**3))
expected=-(k-1)*(k+1)*(2*k**4+8*k**3+9*k*k+6*k+12)/(12*k*(k+2)**2);assert s.simplify(d-expected)==0
out={'wick_trace4':a4,'wick_trace3_squared':a33,'d1':str(d),'small_k':{str(j):str(d.subs(k,j)) for j in range(2,7)}}
print(json.dumps(out,indent=2));Path('root-gue-check.json').write_text(json.dumps(out,indent=2)+'\n')
