from fractions import Fraction as Q
from math import comb
import random,json
random.seed(7813)
def val(x,p):
 x=Q(x);n,d=abs(x.numerator),x.denominator;v=0
 while n%p==0:n//=p;v+=1
 while d%p==0:d//=p;v-=1
 return v
def digits(n,p):
 s=0
 while n:s+=n%p;n//=p
 return s
def solve(E,M):
 t=len(E);V=[[Q(n**i) for n in E]+[Q(M[i])] for i in range(t)]
 for k in range(t):
  z=next(i for i in range(k,t) if V[i][k]);V[k],V[z]=V[z],V[k];pivot=V[k][k];V[k]=[x/pivot for x in V[k]]
  for i in range(t):
   if i!=k:
    pivot=V[i][k];V[i]=[a-pivot*b for a,b in zip(V[i],V[k])]
 return [r[-1] for r in V]
def deep(E,C,p):
 pts=[]
 for k in range(max(E)+1):
  a=sum(c*comb(n,k) for n,c in zip(E,C) if n>=k)
  if a:pts.append((k,val(a,p)))
 H=[]
 for u in pts:
  while len(H)>=2:
   a,b=H[-2:]
   if (b[1]-a[1])*(u[0]-b[0]) >= (u[1]-b[1])*(b[0]-a[0]):H.pop()
   else:break
  H.append(u)
 out=[('inf',pts[0][0])] if pts[0][0] else []
 for a,b in zip(H,H[1:]):
  r=Q(a[1]-b[1],b[0]-a[0])
  if r>Q(1,p-1):out.append((str(r),b[0]-a[0]))
 return out
cases=0;interesting=[]
for p in (2,3,5,7):
 for t in range(2,10):
  D=max(digits(i,p) for i in range(t));A=(D-1+p-2)//(p-1);P=p**A
  for it in range(8):
   E=random.sample(range(0,100),t);seen={};F=[]
   for n in E:
    a=n%P;j=seen.get(a,0);F.append(a+j*P);seen[a]=j+1
   M=[0]*(t-1)+[1] if it==0 else [p**random.randint(3,9)*random.randint(-3,3) for i in range(t-1)]+[1]
   C=solve(E,M);B=solve(F,M);a=deep(E,C,p);b=deep(F,B,p)
   assert a==b,(p,t,E,F,M,a,b)
   cases+=1
   if a and sum(x[1] for x in a)>t-1:interesting.append({'p':p,'t':t,'E':E,'F':F,'roots':a})
print(json.dumps({'cases':cases,'status':'all exact Newton polygons agree above the critical depth','excess_examples':interesting[:8]},indent=2))
