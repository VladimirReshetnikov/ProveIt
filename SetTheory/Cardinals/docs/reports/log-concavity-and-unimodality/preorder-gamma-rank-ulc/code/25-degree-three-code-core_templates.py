from itertools import product,combinations,permutations
from math import factorial
import sympy as s,json
from pathlib import Path
x=s.symbols('x');m=x+3

def preorders(n):
 pairs=[(i,j)for i in range(n)for j in range(n)if i!=j]
 for mask in range(1<<len(pairs)):
  arcs={(i,i)for i in range(n)}|{e for k,e in enumerate(pairs)if mask>>k&1}
  if all((i,k)in arcs for i,j in arcs for a,k in arcs if j==a):yield arcs

def choose(n,k):return s.sympify(s.prod(n-i for i in range(k)))/factorial(k)

def gamma(arcs,lower):
 g=[s.Integer(0)]*4
 for roles in product(range(3),repeat=3):
  A=[i for i in range(3) if roles[i]==1];B=[i for i in range(3) if roles[i]==2]
  for a in range(4):
   for b in range(4-a):
    k=len(A)+a
    if k!=len(B)+b or k>3:continue
    AA=A+list(range(3,3+a));BB=B+list(range(3+a,3+a+b))
    def edge(i,j):
     if i<3 and j<3:return i!=j and (i,j)in arcs
     if i>=3 and j<3:return j not in lower
     if i<3 and j>=3:return i in lower
     return False
    feasible=any(all(edge(i,j)for i,j in zip(AA,p)) for p in permutations(BB))
    if feasible:g[k]+=choose(m,a)*choose(m-a,b)
 return [s.expand(v)for v in g]

def disc(g):
 _,a,b,c=g
 return s.expand(a*a*b*b-4*b**3-4*a**3*c-27*c*c+18*a*b*c)

if __name__=='__main__':
 out={};count=0
 for arcs in preorders(3):
  for mask in range(8):
   lower={i for i in range(3)if mask>>i&1};upper=set(range(3))-lower
   if any((i,j)not in arcs or (j,i)in arcs for i in lower for j in upper):continue
   count+=1;g=gamma(arcs,lower);d=s.factor(disc(g));gaps=[s.factor(g[1]**2-3*g[2]),s.factor(g[2]**2-3*g[1]*g[3])]
   assert all(v>0 for v in s.Poly(d,x).all_coeffs()),(arcs,lower,g,d)
   key=tuple(str(v)for v in g)
   if key not in out:out[key]={'gamma':list(key),'discriminant':str(d),'gaps':[str(v)for v in gaps],'arcs':[e for e in sorted(arcs) if e[0]!=e[1]],'lower':sorted(lower),'count':0}
   out[key]['count']+=1
 print('labeled templates',count,'distinct polynomial templates',len(out))
 for i,row in enumerate(out.values()):print(i,row)
 Path(__file__).with_name('core_certificates.json').write_text(json.dumps(list(out.values()),indent=2)+'\n')
