"""Exact symbolic certificate; Python 3 + SymPy. No numerical root decisions."""
from itertools import combinations, permutations
from math import comb, factorial
from pathlib import Path
import json
import sympy as s
from layered import compositions, gamma
x,z=s.symbols('x z')

def choose_poly(n,k):
 return s.sympify(s.prod(n-j for j in range(k)))/factorial(k)

def symbolic_gamma(layers):
 dp={(0,0):s.Integer(1)}
 for n in layers:
  nd={}
  for (balance,k),v in dp.items():
   for a in range(4-k):
    for b in range(balance+1):
     if isinstance(n,int) and a+b>n:continue
     if balance+a-b>3:continue
     key=(balance+a-b,k+a)
     nd[key]=nd.get(key,0)+v*choose_poly(n,a)*choose_poly(n-a,b)
  dp=nd
 return [s.expand(dp.get((0,k),0)) for k in range(4)]

def discriminant(g):
 _,a,b,c=g
 return a*a*b*b-4*b*b*b-4*a*a*a*c-27*c*c+18*a*b*c

def brute_gamma(layers):
 labels=[i for i,n in enumerate(layers) for _ in range(n)]
 n=len(labels);out=[1,0,0,0]
 for k in range(1,4):
  for A in combinations(range(n),k):
   for B in combinations([j for j in range(n) if j not in A],k):
    out[k]+=any(all(labels[a]<labels[b] for a,b in zip(A,p))for p in permutations(B))
 return out

def main():
 data={'templates':[],'finite':[]}
 # Up to duality, six templates exhaust one large layer + 3 vertices.
 patterns=[(x+3,3),(x+3,1,2),(x+3,2,1),(1,x+3,2),(x+3,1,1,1),(1,x+3,1,1)]
 for c in patterns:
  g=symbolic_gamma(c)
  disc=s.factor(discriminant(g))
  gaps=[s.expand(g[1]**2-3*g[2]),s.expand(g[2]**2-3*g[1]*g[3])]
  assert all(v>0 for v in s.Poly(s.expand(disc),x).all_coeffs())
  assert all(all(v>0 for v in s.Poly(p,x).all_coeffs()) for p in gaps)
  for m in range(3,13):
   sizes=tuple(int(s.sympify(a).subs(x,m-3))for a in c)
   assert [int(a.subs(x,m-3)) for a in g]==gamma(sizes)
  data['templates'].append({'layers':[str(a)for a in c],'gamma':[str(a)for a in g],'discriminant':str(disc),'gaps':[str(s.factor(a))for a in gaps]})
 for n in (6,7):
  for c in compositions(n):
   g=gamma(c)
   assert g==brute_gamma(c),('DP versus direct matching',c,g)
   if max(c)>=n-3:continue
   disc=discriminant(g)
   assert g[3]>0 and disc>0
   data['finite'].append({'layers':c,'gamma':g,'discriminant':disc,'gaps':[g[1]**2-3*g[2],g[2]**2-3*g[1]*g[3]]})
 p=Path(__file__).with_name('layered_certificates.json');p.write_text(json.dumps(data,indent=2)+'\n')
 for n in (6,7):
  rows=[r for r in data['finite'] if sum(r['layers'])==n]
  print('n',n,'exceptional compositions',len(rows),'min discriminant',min(r['discriminant'] for r in rows))
 print('Six symbolic families, 57 finite exceptional compositions, and 96 independent direct matching checks passed.')

if __name__=='__main__':main()
