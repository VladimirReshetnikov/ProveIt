from fractions import Fraction as F
from math import factorial

def recurrence(k,nmax,kind):
 q=k-1;D={(x,0):F(1) for x in range(q*nmax+1)}
 if kind=='dfa':D[-1,0]=F(1)
 for m in range(1,nmax+1):
  for x in range(q*m,q*nmax+1):
   vert=2 if kind=='dfa' else 1
   defect=m if kind=='dfa' else m-1 if kind=='compact' else 0
   D[x,m]=vert*D.get((x,m-1),0)+(m+1)*D.get((x-1,m),0)-defect*D.get((x-k,m-1),0)
 return D

def positive_runs(k,n,kind):
 q=k-1;states={0:F(1)}
 for m in range(n):
  nxt={}
  for x,val in states.items():
   for ell in range(max(0,q*(m+1)-x),q*n-x+1):
    w=F((m+1)**ell)
    if kind=='dfa':
     if m==0:w/=2
     elif ell>=k:w*=1-F(1,2*(m+1)**q)
    elif kind=='compact' and ell>=k:w*=1-F(m,(m+1)**k)
    nxt[x+ell]=nxt.get(x+ell,0)+val*w
  states=nxt
 return states.get(q*n,0)
checks=0
for k in range(3,9):
 q=k-1
 for kind in ['relaxed','compact','dfa']:
  D=recurrence(k,7,kind)
  for n in range(1,8):
   run=positive_runs(k,n,kind)
   val=D[q*n,n]/(2**n if kind=='dfa' else 1)
   assert run==val,(k,kind,n,run,val)
   checks+=1
  if kind=='dfa':
   for x in range(q,q*7+1):assert D[x,1]==2**(x-q+1)-1
  # Initial transformed vectors, and exact signed recurrence.
  d={}
  for (x,m),value in D.items():
   if x<0:continue
   i=x+m;j=x-q*m
   d[i,j]=F(q**(2*x),factorial(x))*value/(2**m if kind=='dfa' else 1)
  for i in range(k+1):
   assert d[i,i]==F(q**(2*i),factorial(i))
  assert d[k,0]==F(q**(2*q),factorial(q)*(2 if kind=='dfa' else 1))
  for (i,j),value in d.items():
   if i<k+1:continue
   x=(q*i+j)//k;m=(i-j)//k
   U=F(q*q*(i-j+k),q*i+j)
   rhs=U*d.get((i-1,j-1),0)+d.get((i-1,j+q),0)
   if kind!='relaxed' and m>=1:
    defect=F(m,2) if kind=='dfa' else F(m-1)
    beta=defect*F(q**(2*k)*factorial(x-k),factorial(x))
    rhs-=beta*d.get((i-k-1,j-1),0)
   assert value==rhs,(k,kind,i,j,value,rhs)
   checks+=1
print('PASS:',checks,'exact checks, k=3..8, n<=7: source seeds, completed runs, signed transforms')
