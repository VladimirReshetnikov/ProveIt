from fractions import Fraction as F
import json

def vp(x,p):
 if not x:raise ValueError('zero')
 if isinstance(x,F):return vp(x.numerator,p)-vp(x.denominator,p)
 n=0
 while x%p==0:n+=1;x//=p
 return n
N=60;counts=[0,0];h=[F(1)]+[F((-1)**(j-1),j*(j+1)) for j in range(1,N+1)]
for Y in range(1,121):
 a=[F(1)]
 for n in range(1,N+1):a.append(sum(F((Y+1)*j-n,n)*h[j]*a[n-j] for j in range(1,n+1)))
 for p in [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61]:
  e=vp(Y,p)
  for m in range(1,N//(p-1)+1):
   r=(p-1)*m
   if m<=p**e:
    assert a[r] and vp(a[r],p)==e-vp(m,p)-m,(Y,p,m,'principal')
    counts[0]+=1
   r+=1
   if p>2 and r<=N and m<p**e and r%p:
    assert a[r] and vp(a[r],p)==e-m,(Y,p,m,'shifted')
    counts[1]+=1
print(json.dumps({'method':'independent rational power recurrence','Y_range':[1,120],'max_defect':60,'principal_checks':counts[0],'shifted_checks':counts[1],'status':'PASS'}))
