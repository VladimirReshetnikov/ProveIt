"""Exact bounded screen of a restricted first/main Pell subfamily."""
from math import gcd
count=0;positive=0;divisible=0
for q in range(2,7):
 for n in range(1,5):
  Y=q**3*n
  for X in range(1,101):
   t=X*Y*Y;D=t*(t+1);x0=2*t+1;ks=[];x,k=1,0
   for _ in range(5):
    x,k=x*x0+k*2*D,x*2+k*x0;ks.append((x,k))
   a=Y*(X+1);D2=a*a+4*a+3;u0=a+2;ys=[];d,c=1,0
   for _ in range(16):
    d,c=d*u0+c*D2,d+c*u0;ys.append((d,c))
   H=3+4*a;U=Y*q*q
   for x,k in ks:
    assert x*x-D*k*k==1
    for d,c in ys:
     count+=1;assert d*d-D2*c*c==1
     eta=c-Y*k
     if not 1<=eta<k:continue
     positive+=1;L=X+a*c
     for sign in (1,-1):
      if U*(sign*d-L)%H==0:
       divisible+=1;print('POTENTIAL',q,n,X,'first_root',x,'k',k,'d',d,'c',c,'sign',sign,flush=True)
print('done; combinations',count,'positive_eta_zeta',positive,'main_divisibility_passes',divisible,flush=True)
