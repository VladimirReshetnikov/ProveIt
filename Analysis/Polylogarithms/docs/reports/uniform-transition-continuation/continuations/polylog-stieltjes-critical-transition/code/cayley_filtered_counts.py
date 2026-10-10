from fractions import Fraction as Q
from math import factorial,comb,gcd
from collections import defaultdict

def mobius(n):
 s=1;p=2
 while p*p<=n:
  if n%p==0:
   n//=p;s=-s
   if n%p==0:return 0
   while n%p==0:n//=p
  p+=1
 return -s if n>1 else s

def divs(n):return [d for d in range(1,n+1) if n%d==0]
def W(n,p,q,e):
 out=0
 for d in divs(gcd(gcd(n,p),q)):
  a,b,c=n//d,p//d,q//d;r=a-b-c
  out+=mobius(d)*comb(a,b)*comb(a-b,c)*(2+e**d)**r
 return Q(out,n)
def T(n,p,e):
 out=0
 for d in divs(n):
  mu=mobius(d)
  if d%2:
   if p==0:out+=mu*e**n
  elif (2*p)%d==0 and 2*p<=n:
   j=2*p//d
   out+=mu*comb(n//d,j)*2**j*3**(n//d-j)
 return (-1)**(n-1)*Q(out,n)
def generators(N):
 out=defaultdict(int)
 out[(1,1,0)]=out[(1,1,1)]=1
 for n in range(2,N+1):
  for p in range(n+1):
   for q in range(n-p+1):
    if p<q:continue
    d1,dk=W(n,p,q,1),W(n,p,q,-1)
    even,odd=(d1+dk)/2,(d1-dk)/2
    if p==q:
     c,ck=T(n,p,1),T(n,p,-1)
     even=(even+(c+ck)/2)/2;odd=(odd+(c-ck)/2)/2
    for par,cnt in enumerate((even,odd)):
     assert cnt.denominator==1 and cnt>=0,(n,p,q,par,cnt)
     out[(n,n-p,par)]+=int(cnt)
 return {k:v for k,v in out.items() if v}
def hilbert(N):
 gs=generators(N);out={(0,0,0):1}
 for (n,d,par),g in sorted(gs.items()):
  z=defaultdict(int)
  for (a,b,c),v in out.items():
   for k in range((N-a)//n+1):
    z[(a+k*n,b+k*d,(c+k*par)%2)]+=v*comb(g+k-1,k)
  out=dict(z)
 return gs,out
if __name__=='__main__':
 gs,h=hilbert(10)
 for n in range(1,11):
  print(n,'odd',[h.get((n,d,1),0) for d in range(1,n+1)],'total',sum(v for (a,b,c),v in h.items() if a==n and c==1))
 print('n7gens',[(k,v) for k,v in sorted(gs.items()) if k[0]==7])
