from itertools import product
from math import comb
import sympy as s

def compositions(n):
 if n==0: yield (); return
 for j in range(1,n+1):
  for c in compositions(n-j):yield (j,)+c

def gamma(layers):
 # Each level chooses a tails and b heads. All heads need earlier unmatched tails.
 dp={(0,0):1}
 for n in layers:
  nd={}
  for (balance,k),v in dp.items():
   for a in range(min(n,3-k)+1):
    for b in range(min(n-a,balance)+1):
     if balance+a-b>3:continue
     key=(balance+a-b,k+a)
     nd[key]=nd.get(key,0)+v*comb(n,a)*comb(n-a,b)
  dp=nd
 return [dp.get((0,k),0) for k in range(4)]

if __name__=='__main__':
 x=s.symbols('x',integer=True,nonnegative=True)
 templates=[]
 for total in range(1,4):
  for c in compositions(total):
   for pos in range(len(c)+1):
    vals=[gamma(c[:pos]+(m,)+c[pos:]) for m in range(3,10)]
    polys=[s.interpolate([(m-3,v[k])for m,v in zip(range(3,10),vals)],x).expand() for k in range(4)]
    gaps=[s.expand(polys[1]**2-3*polys[2]),s.expand(polys[2]**2-3*polys[1]*polys[3])]
    if total==3:
     print(c,pos,'gamma=',polys,'gaps=',[s.factor(g)for g in gaps])
     assert all(all(co>=0 for co in s.Poly(g,x).all_coeffs()) for g in gaps)
    templates.append((c,pos,polys,gaps))
 for n in range(6,8):
  for c in compositions(n):
   g=gamma(c)
   if not g[3]:continue
   assert g[1]**2>=3*g[2] and g[2]**2>=3*g[1]*g[3],(c,g)
 print('ALL OK')
