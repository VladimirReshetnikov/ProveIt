"""Independent direct cube evaluation against the exact Fourier certificate."""
from cmath import exp
from itertools import product
from fractions import Fraction
from verify_dual_gap import enumerate_dual, evaluate, dual_bounds

if not __debug__:
    raise RuntimeError('Verification requires assertions; do not use python -O or -OO.')

vertices=list(product((0,1),repeat=4))[1:]
worst=0.0
cases=0
for n in [5,7,9,11,13]:
 coeff=enumerate_dual(n if n<13 else None)
 t=Fraction(-7,50) if n==5 else Fraction(-1,7)
 ds=evaluate(coeff,t)
 for theta in [.173,.613]:
  z=[exp(1j*(theta+2*3.141592653589793*x/n)) for x in range(n)]
  g=[(q+q.conjugate()+float(t)*(q**3+q.conjugate()**3)).real for q in z]
  for x in [0,1,n-1]:
   total=0.
   for hs in product(range(n),repeat=4):
    term=1.
    for v in vertices:
     term*=g[(x+sum(h*w for h,w in zip(hs,v)))%n]
    total+=term
   direct=total/n**4
   polynomial=sum(float(d)*(z[x]**k+z[x].conjugate()**k).real for k,d in ds.items())
   error=abs(direct-polynomial)/max(1.,abs(direct))
   assert error<1e-10,(n,theta,x,direct,polynomial,error)
   worst=max(worst,error);cases+=1
print('Direct cube versus Fourier dual:',cases,'cases; max relative error',worst)
