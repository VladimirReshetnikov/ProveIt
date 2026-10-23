import json,math
from pathlib import Path
from collections import defaultdict
import sympy as s
T=json.loads(Path('diophantine_zfc_round5/coefficients/wang943_tiles.json').read_text());widths=(9,10,9,10);starts=(0,9,19,28);offsets=(1020,1000,980,960);c={}
for i,tile in enumerate(T):c[i]=1+sum((1<<(10+2*(starts[t]+j))) for t,x in enumerate(tile) for j in range(widths[t]) if ((x+(1<<(widths[t]-1)))>>j)&1)+sum(1<<(10+2*j) for j in range(38,42))
for t,o in enumerate(offsets):
 for j in range(widths[t]):c[o+2*j]=1<<(10+2*(starts[t]+j))
for j,a in enumerate((1095,1096,2195,3296)):c[a]=1<<(10+2*(38+j))
c.update({1063:0,1064:0});E=set(c);dc=defaultdict(int)
for a in(40,41,1100,2200):dc[a]+=1
for e,v in c.items():
 for target in(4393,5495):dc[target-e]+=v
b=119;L=8801;d=b*L;mass=(len(E)+2)*(2*sum(c.values())+6)
print('size',len(E),'mass threshold',mass.bit_length(),(4*mass+8).bit_length(),'d',d)
fac=s.factorint(d);print('factors',fac)
def unit(p):
 rho=pow(2,b,p);B=pow(2,d,p);DC=sum(v*pow(rho,e,p) for e,v in dc.items())%p
 return B,(B*B-1)%p,(1+B*DC+B*B*(rho+1))%p
print('units',{p:unit(p) for p in fac})
if all(all(unit(p)[1:]) for p in fac):
 orders={int(p**a):int(s.n_order(pow(2,d,int(p**a)),int(p**a))) for p,a in fac.items()};k0=math.lcm(*orders.values());print('orders',orders,k0)
 for m in range(1,100000):
  lam=k0*m+1
  if s.isprime(lam) and d%lam and all(unit(lam)[1:]) and pow(2,d*(lam-1),lam*lam)!=1:print('lambda',lam,'lift',pow(2,d*(lam-1),lam*lam));break
