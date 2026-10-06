from decimal import Decimal as D, getcontext
from fractions import Fraction
getcontext().prec=65

def bernoulli(n):
 a=[Fraction(0)]*(n+1)
 for m in range(n+1):
  a[m]=Fraction(1,m+1)
  for j in range(m,0,-1):a[j-1]=j*(a[j-1]-a[j])
 return a[0]

def tail(al,ki):
 k=D(ki)
 if k<100:return sum((D(j)**(-al) for j in range(int(k)+1,101)),D(0))+tail(al,100)
 z=k**(1-al)/(al-1)-k**(-al)/2
 rising=al; factorial=2
 for m in range(1,15):
  if m>1:
   rising*= (al+2*m-3)*(al+2*m-2)
   factorial*= (2*m-1)*(2*m)
  b=bernoulli(2*m)
  z+=D(b.numerator)/D(b.denominator*factorial)*rising*k**(-al-2*m+1)
 return z

def run():
 for al in map(D,['1.3','1.5','2','2.5','3','5']):
  C=1/(1+tail(al,1))
  for eta in map(D,['1e-5','1e-8','1e-11']):
   K=(C/eta)**(1/al); ep=eta*K
   def b(k):return 1-2*C*tail(al,k)
   def h(k):return C*D(k)**(-al)/b(k)
   lo=0; hi=max(1,int(K*D('1.5'))+20)
   while b(hi)<=0 or h(hi)>=eta:hi*=2
   while hi-lo>1:
    mid=(lo+hi)//2
    if b(mid)<=0 or h(mid)>=eta:lo=mid
    else:hi=mid
   k=lo
   L=(1-(1-2*eta)**k*b(k))/2
   s=D(1)+2*ep/(al*(al-1))
   for j in range(25):s-=(s**al-2*ep*s/(al-1)-1)/(al*s**(al-1)-2*ep/(al-1))
   M=s**(-al)*(-2*ep*s).exp(); E=(1-M)/2
   u=K*s-int(K*s); B2=u*u-u+D(1)/6
   env=E+eta*M*(ep*s-D('.5'))
   resid=(L-env)/(eta/K); Bcoef=al/2*B2
   two=al/(al-1)*ep-(al+1)/(al-1)*ep*ep-eta/2
   scale=ep**3+eta*ep+eta/K
   print('alpha',al,'eta',eta,'k',k,'u',f'{u:.5g}','env residual',f'{resid:.8g}','Bcoef',f'{Bcoef:.8g}','difference',f'{resid-Bcoef:.4g}','two normalized error',f'{(L-two)/scale:.6g}')
if __name__=='__main__':run()
