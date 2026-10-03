from fractions import Fraction as F
from math import factorial

def weights(q,N):
    k=q+1;l=[F(k,2)]
    for j in range(N):
        l.append((k*l[j]-(l[j-q] if j>=q else 0))/q)
    return l,[x/F(j+1) for j,x in enumerate(l)]

checks=0
for q in range(2,11):
 k=q+1;l,w=weights(q,100)
 assert all(1<=x<=q for x in w)
 for j in range(80):
  assert q*l[j+1]+(l[j-q] if j>=q else 0)==k*l[j]
 for r in range(k):
  u={j:F((j*7+3)%11-5,7) for j in range(r,60,k)}
  h=lambda j:j+1
  norm=lambda a:sum(w[j]*a[j]**2 for j in a)
  Tu={j:q*u.get(j-1,0)+u.get(j+q,0) for j in range((r+1)%k,70,k)}
  defect=k*k*norm(u)-norm(Tu)
  var=sum(q*w[j]*j*(j+k)*(u.get(j-1,0)/F(j)-u.get(j+q,0)/F(j+k))**2 for j in Tu if j>=1)
  assert defect==var,(q,r,defect,var)
  phase=list(range(r,70,k))
  radial=sum(F(h(j)*h(j+k))*(u.get(j+k,0)/F(h(j+k))-u.get(j,0)/F(h(j)))**2 for j in phase)
  grad=sum((u.get(j+k,0)-u.get(j,0))**2 for j in phase)+F(k,r+1)*u.get(r,0)**2
  assert radial==grad
  checks+=2
 for i in range(k+2,50):
  alpha=1+F(q*q-1,q*i+1)
  for t in range((i-1)%k,i,k):
   v=F(q*k*(t+1-q),q*i+t+1)
   loss=(alpha-1+v*l[t+1]/(k*l[t]))/alpha
   assert loss>=0
   if t<=q-1:
    assert loss==F(k*t*(q*i+q),(q*i+1)*(q*i+t+1))/alpha
   checks+=1
print('PASS:',checks,'exact rational phase-form and confined-column checks; q=2..10')
